import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Use
import Mathlib.Tactic.CongrExclamation
import Mathlib.Data.List.Induction

import LeanYjs.ListLemmas
import LeanYjs.Network.HbClosed

open List

section hb_consistent

variable {A : Type} [DecidableEq A] (hb : CausalOrder A)

inductive hb_consistent : List A → Prop where
  | nil : hb_consistent []
  | cons : ∀ (a : A) (ops : List A),
      hb_consistent ops →
      (∀ b, b ∈ ops → ¬ b ≤ a) →
      hb_consistent (a :: ops)

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

omit [DecidableEq A] in lemma hb_consistent_tail (a : A) (ops : List A) :
  (h_consistent : hb_consistent hb (a :: ops)) →
  hb_consistent hb ops := by
  intro h_consistent
  cases h_consistent
  assumption

end hb_consistent

section effect

class WithId (A : Type) (S : outParam Type) [DecidableEq S] where
  id : A → S

def IdNoDup {A : Type} {S : Type} [DecidableEq S] [WithId A S] (ops : List A) : Prop :=
  List.Pairwise (fun a b => WithId.id a ≠ WithId.id b) ops

class Operation (A : Type) where
  State : Type
  Error : Type
  init : State
  effect : A → State → Except Error State
  isValidState : A → State → Prop
  StateInv : State → Prop := fun _ => True
  stateInv_init : StateInv init := by trivial
  stateInv_effect : ∀ (op : A) (s s' : State),
    StateInv s →
    isValidState op s →
    effect op s = Except.ok s' →
    StateInv s' := by
      intro _ _ _ _ _ _
      trivial

def effect_list [Operation A] (ops : List A) (s : Operation.State A) :=
  foldlM (fun s op => Operation.effect op s) s ops

@[simp, grind =] theorem effect_list_nil [Operation A] (s : Operation.State A) :
  effect_list [] s = Except.ok s := by rfl

@[simp, grind =] theorem effect_list_cons [Operation A] (a : A) (ops : List A)
  (s : Operation.State A) :
  effect_list (a :: ops) s = (do let s <- Operation.effect a s; effect_list ops s) := by rfl

@[simp, grind =] theorem effect_list_append [Operation A](ops₀ ops₁ : List A)
  (s : Operation.State A) :
  effect_list (ops₀ ++ ops₁) s = (do let s <- effect_list ops₀ s; effect_list ops₁ s) := by
  induction ops₀ with
  | nil =>
    simp [effect_list]
  | cons a ops₀ ih =>
    simp [effect_list]

class MonotoneOperation (A : Type) {hb : CausalOrder A} (S : outParam Type) [DecidableEq S] [WithId A S] [Operation A]  [Operation A] where
  StateSource : A → Prop := fun _ => True
  -- TODO: is this enough to strong assumption for yjs?
  isValidState_mono : ∀ {l : List A},
    StateSource a →
    (∀x < a, x ∈ l) →
    hb_consistent hb l →
    hbClosed hb l →
    effect_list l Operation.init = Except.ok s →
    IdNoDup l →
    Operation.isValidState a s
end effect

section commutativity

variable {A : Type} [DecidableEq A] {S : Type} [DecidableEq S] {hb : CausalOrder A}
variable [WithId A S]  [Operation A]

def concurrent_commutative (list : List A) : Prop :=
  ∀ a b (s s' : Operation.State A), a ∈ list → b ∈ list → hb_concurrent hb a b →
    Operation.StateInv s →
    Operation.isValidState a s →
    Operation.isValidState b s →
    (Operation.effect a s >>= Operation.effect b) = Except.ok s' → (Operation.effect b s >>= Operation.effect a) = Except.ok s'

theorem Except.bind_eq_ok_exist' {α β : Type} {e : Except α β} {f : β → Except α β'} {v : β'} :
  e >>= f = Except.ok v →
  ∃ u : β, e = Except.ok u ∧ f u = Except.ok v := by
  intro h
  cases e with
  | error err =>
    simp [bind, Except.bind] at h
  | ok u =>
    refine ⟨u, rfl, ?_⟩
    exact h

theorem effect_list_stateInv [MonotoneOperation A (hb := hb) S] :
  ∀ {ops : List A} {s : Operation.State A},
    (∀ op, op ∈ ops → MonotoneOperation.StateSource (A := A) (hb := hb) op) →
    hb_consistent hb ops →
    hbClosed hb ops →
    IdNoDup ops →
    effect_list ops Operation.init = Except.ok s →
    Operation.StateInv s := by
  intro ops s h_source h_consistent h_closed h_no_dup h_effect
  induction ops using List.reverseRecOn generalizing s with
  | nil =>
    cases h_effect
    exact Operation.stateInv_init (A := A)
  | append_singleton ops a ih =>
    have h_consistent_ops : hb_consistent hb ops := by
      apply hb_consistent_sublist (hb := hb) h_consistent
      grind
    have h_closed_ops : hbClosed hb ops := by
      intro x y l₁ l₂ h_eq h_lt
      apply h_closed x y l₁ (l₂ ++ [a])
      · simpa [List.append_assoc, h_eq]
      · exact h_lt
    have h_no_dup_ops : IdNoDup ops := by
      grind [IdNoDup]
    have h_effect' :
      (do
        let s ← effect_list ops Operation.init
        let s ← Operation.effect a s
        Except.ok s) = Except.ok s := by
      simpa [effect_list_append] using h_effect
    obtain ⟨ s_prev, h_prefix, h_last' ⟩ := Except.bind_eq_ok_exist' h_effect'
    have h_last : Operation.effect a s_prev = Except.ok s := by
      obtain ⟨ s_after, h_last_ok, h_last_eq ⟩ := Except.bind_eq_ok_exist' h_last'
      have hs_after : s_after = s := by
        simpa using h_last_eq
      subst hs_after
      exact h_last_ok
    have h_stateInv_prev : Operation.StateInv s_prev :=
      ih
        (by
          intro op hop
          exact h_source op (by simp [hop]))
        h_consistent_ops h_closed_ops h_no_dup_ops h_prefix
    have h_valid_a : Operation.isValidState a s_prev := by
      refine MonotoneOperation.isValidState_mono (hb := hb) (a := a) (s := s_prev)
        (l := ops) ?_ ?_ h_consistent_ops h_closed_ops h_prefix h_no_dup_ops
      · exact h_source a (by simp)
      intro x hx_lt
      exact h_closed a x ops [] (by simp) hx_lt
    exact Operation.stateInv_effect (A := A) a s_prev s h_stateInv_prev h_valid_a h_last

@[grind .] theorem hb_consistent_concurrent (a : A) (ops₀ ops₁ : List A) :
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

theorem Except.bind_eq_ok_exist {α β : Type} {e : Except α β} {f : β → Except α β'} {v : β'} :
  e >>= f = Except.ok v →
  ∃ u : β, e = Except.ok u ∧ f u = Except.ok v := by
  intros h
  cases e with
  | error err =>
    simp [bind, Except.bind] at *
  | ok u =>
    refine ⟨ u, by rfl, ?_ ⟩
    assumption

theorem Except.ok_bind {α β ε : Type} (x : α) (f : α -> Except β ε) :
  (do
    let x <- Except.ok x
    f x) = f x := by eq_refl

-- Swapping adjacent concurrent elements preserves hb_consistent.
theorem hb_consistent_swap (ops₀ ops₁ : List A) (a b : A) :
  hb_consistent hb (ops₀ ++ a :: b :: ops₁) →
  hb_concurrent hb b a →
  hb_consistent hb (ops₀ ++ b :: a :: ops₁) := by
  intro h_consistent h_concurrent
  induction ops₀ with
  | nil =>
    -- h_consistent : hb_consistent hb (a :: b :: ops₁)
    cases h_consistent with
    | cons _ _ h_tail h_no_lt_a =>
      -- h_tail : hb_consistent hb (b :: ops₁)
      have h_tail' : hb_consistent hb ops₁ := by
        exact hb_consistent_tail (hb := hb) b ops₁ h_tail
      have h_no_lt_b : ∀ x, x ∈ ops₁ → ¬ x ≤ b := by
        cases h_tail with
        | cons _ _ _ h_no_lt_b =>
          intro x hx hle
          apply h_no_lt_b x (by simp [hx]) hle
      have h_a_ops₁ : hb_consistent hb (a :: ops₁) := by
        apply hb_consistent.cons
        · exact h_tail'
        · intro x hx hle
          apply h_no_lt_a x (by simp [hx]) hle
      apply hb_consistent.cons
      · exact h_a_ops₁
      · intro x hx hle
        simp [List.mem_append] at hx
        rcases hx with hx | hx
        · -- x = a
          subst hx
          exact (h_concurrent.2 hle)
        · -- x ∈ ops₁
          exact h_no_lt_b x hx hle
  | cons x xs ih =>
    -- h_consistent : hb_consistent hb (x :: xs ++ a :: b :: ops₁)
    cases h_consistent with
    | cons _ _ h_tail h_no_lt_x =>
      have h_tail' : hb_consistent hb (xs ++ b :: a :: ops₁) := by
        exact ih h_tail
      apply hb_consistent.cons
      · exact h_tail'
      · intro y hy hle
        -- y ∈ xs ++ b :: a :: ops₁ -> y ∈ xs ++ a :: b :: ops₁
        have hy' : y ∈ xs ++ a :: b :: ops₁ := by
          simp [List.mem_append] at hy
          rcases hy with hy | hy
          · exact by
              simp [List.mem_append, hy]
          · rcases hy with hy | hy
            · -- y = b
              subst hy
              simp [List.mem_append]
            · rcases hy with hy | hy
              · -- y = a
                subst hy
                simp [List.mem_append]
              · -- y ∈ ops₁
                simp [List.mem_append, hy]
        exact h_no_lt_x y hy' hle

theorem hb_concurrent_effect_list_reorder [MonotoneOperation A (hb := hb) S] :
  (∀ x, x ∈ (ops₀ ++ a :: ops₁) → MonotoneOperation.StateSource (A := A) (hb := hb) x) →
  concurrent_commutative (hb := hb) (ops₀ ++ a :: ops₁) →
  (∀ x ∈ ops₁, hb_concurrent hb x a) →
  hb_consistent hb (ops₀ ++ a :: ops₁) →
  hbClosed hb (ops₀ ++ a :: ops₁) →
  IdNoDup (ops₀ ++ a :: ops₁) →
  (do let s <- effect_list ops₀ Operation.init >>= Operation.effect a; effect_list ops₁ s) = Except.ok s →
  (do let s <- effect_list ops₀ Operation.init; effect_list ops₁ s) >>= Operation.effect a = Except.ok s := by
  induction ops₁ generalizing ops₀ with
  | nil =>
    intro _h_source
    simp [effect_list]
  | cons b ops₁ ih =>
    intro h_source h_comm h_concurrent h_consistent h_closed h_no_dup heq
    simp at *
    have ⟨ s', h ⟩ : ∃ s, (effect_list ops₀ Operation.init >>= fun x => Operation.effect a x >>= Operation.effect b) = Except.ok s := by
      have h : (do
        let s <- (do
          let x ← effect_list ops₀ Operation.init
          let s ← Operation.effect a x
          Operation.effect b s)
        effect_list ops₁ s) = Except.ok s := by
        simp; assumption
      grind [Except.bind_eq_ok_exist]
    obtain ⟨ u, h_effects_eq, h_effect_b_eq ⟩ := Except.bind_eq_ok_exist h
    have h_stateInv_u : Operation.StateInv u := by
      apply effect_list_stateInv (hb := hb) (S := S) (ops := ops₀)
      · intro x hx
        exact h_source x (by simp [hx])
      · apply hb_consistent_sublist (hb := hb) h_consistent
        grind
      · grind [hbClosed]
      · grind [IdNoDup]
      · exact h_effects_eq
    have hba : (Operation.effect b u >>= Operation.effect a) = Except.ok s' := by
      apply h_comm a b u s'
      . simp
      . simp
      . grind [hb_concurrent_symm]
      . exact h_stateInv_u
      . refine MonotoneOperation.isValidState_mono (hb := hb) (a := a) (s := u) (l := ops₀)
          ?_ ?_ ?_ ?_ h_effects_eq ?_
        · exact h_source a (by simp)
        · intro x hxlt
          exact h_closed a x ops₀ (b :: ops₁) (by simp [List.append_assoc]) hxlt
        · grind [hb_consistent_sublist]
        · grind [hbClosed]
        · grind [IdNoDup]
      . refine MonotoneOperation.isValidState_mono (hb := hb) (a := b) (s := u) (l := ops₀)
          ?_ ?_ ?_ ?_ h_effects_eq ?_
        · exact h_source b (by simp)
        · intros x hxlt
          have h : ¬ a < b := by
            grind [hb_concurrent]
          have h := h_closed b x (ops₀ ++ [a]) ops₁ (by simp) hxlt
          grind
        · grind [hb_consistent_sublist]
        · grind [hbClosed]
        · grind [IdNoDup]
      . assumption
    have ⟨ sb, h_sb ⟩ : ∃ sb, Operation.effect b u = Except.ok sb := by
      apply Except.bind_eq_ok_exist at hba
      grind
    rw [h_effects_eq] at heq |-
    rw [Except.ok_bind, ←bind_assoc, h_effect_b_eq, ←hba] at heq
    simp at heq
    have heq' : (do
      let x ← Operation.effect b u
      let s ← Operation.effect a x
      effect_list ops₁ s) =
    (do
      let s ← effect_list (ops₀ ++ [b]) Operation.init
      let s <- Operation.effect a s
      effect_list ops₁ s) :=
      by
      simp
      rw [h_effects_eq]; rfl
    rw [heq'] at heq
    apply ih at heq
    . simp at heq
      rw [h_effects_eq] at heq
      assumption
    . intro x hx
      exact h_source x (by
        simp [List.mem_append] at hx ⊢
        tauto)
    . grind [concurrent_commutative]
    . grind
    . -- swap a and b using concurrency to preserve hb_consistent
      have h_concurrent_ba : hb_concurrent hb b a := h_concurrent.1
      have h_swapped : hb_consistent hb (ops₀ ++ b :: a :: ops₁) := by
        apply hb_consistent_swap (hb := hb) ops₀ ops₁ a b
        · simpa using h_consistent
        · exact h_concurrent_ba
      simpa [List.append_assoc] using h_swapped
    . -- swap a and b using concurrency to preserve hbClosed
      have h_concurrent_ba : hb_concurrent hb b a := h_concurrent.1
      have h_swapped : hbClosed hb (ops₀ ++ b :: a :: ops₁) := by
        apply hbClosed_swap (hb := hb) ops₀ ops₁ a b
        · simpa using h_closed
        · exact h_concurrent_ba
      simpa [List.append_assoc] using h_swapped
    . grind [IdNoDup]

theorem mem_ops0_prefix_iff_ops1
  (ops₀_first ops₀_last ops₁ : List A) (a b : A)
  (no_dup₀ : IdNoDup (ops₀_first ++ b :: ops₀_last ++ [a]))
  (no_dup₁ : IdNoDup (ops₁ ++ [b]))
  (h_mem : ∀ x, x ∈ ops₀_first ++ b :: ops₀_last ++ [a] ↔ x ∈ ops₁ ++ [b]) :
  ∀ x, x ∈ ops₀_first ++ ops₀_last ++ [a] ↔ x ∈ ops₁ := by
  intro x
  -- b ∉ ops₁
  have hb_not_in_ops1 : b ∉ ops₁ := by
    have hpair : List.Pairwise (fun x y => WithId.id x ≠ WithId.id y) (ops₁ ++ [b]) := no_dup₁
    rw [List.pairwise_append] at hpair
    rcases hpair with ⟨ _, _, hrel ⟩
    intro hb_mem
    have hneq := hrel b hb_mem b (by simp)
    exact hneq rfl
  -- b ∉ ops₀_first
  have hb_not_in_first : b ∉ ops₀_first := by
    have hpair : List.Pairwise (fun x y => WithId.id x ≠ WithId.id y)
      (ops₀_first ++ (b :: ops₀_last ++ [a])) := by
      simpa [List.append_assoc] using no_dup₀
    rw [List.pairwise_append] at hpair
    rcases hpair with ⟨ _, _, hrel ⟩
    intro hb_mem
    have hneq := hrel b hb_mem b (by simp)
    exact hneq rfl
  have hb_not_in_rest : b ∉ ops₀_last ++ [a] := by
    have hpair : List.Pairwise (fun x y => WithId.id x ≠ WithId.id y)
      (ops₀_first ++ (b :: ops₀_last ++ [a])) := by
      simpa [List.append_assoc] using no_dup₀
    rw [List.pairwise_append] at hpair
    rcases hpair with ⟨ _, hpair_rest, _ ⟩
    have hrelb : ∀ x ∈ ops₀_last ++ [a], WithId.id b ≠ WithId.id x := by
      have h := (List.pairwise_cons).1 hpair_rest
      exact h.1
    intro hb_mem
    have hneq := hrelb b hb_mem
    exact hneq rfl
  have hb_not_in_all : b ∉ ops₀_first ++ ops₀_last ++ [a] := by
    intro hb_mem
    have hb_mem' : b ∈ ops₀_first ∨ b ∈ ops₀_last ++ [a] := by
      simpa [List.mem_append] using hb_mem
    cases hb_mem' with
    | inl hmem => exact hb_not_in_first hmem
    | inr hmem => exact hb_not_in_rest hmem
  constructor
  · intro hx
    have hx' : x ∈ ops₀_first ++ b :: ops₀_last ++ [a] := by
      have hx' : x ∈ ops₀_first ∨ x ∈ ops₀_last ++ [a] := by
        simpa [List.mem_append, List.append_assoc] using hx
      have hx'' : x ∈ ops₀_first ∨ x ∈ (b :: ops₀_last ++ [a]) := by
        cases hx' with
        | inl hmem => exact Or.inl hmem
        | inr hmem => exact Or.inr (by simp [hmem])
      have hx''' : x ∈ ops₀_first ++ (b :: ops₀_last ++ [a]) := (List.mem_append).2 hx''
      simpa [List.append_assoc] using hx'''
    have hx'' : x ∈ ops₁ ++ [b] := (h_mem x).1 hx'
    have hx_ne_b : x ≠ b := by
      intro hxb
      subst hxb
      exact hb_not_in_all hx
    have hx_ops1 : x ∈ ops₁ := by
      have hx'' : x ∈ ops₁ ∨ x = b := by
        simpa [List.mem_append] using hx''
      cases hx'' with
      | inl hmem => exact hmem
      | inr hxb => cases hx_ne_b hxb
    exact hx_ops1
  · intro hx
    have hx' : x ∈ ops₁ ++ [b] := by
      exact (List.mem_append).2 (Or.inl hx)
    have hx'' : x ∈ ops₀_first ++ b :: ops₀_last ++ [a] := (h_mem x).2 hx'
    have hx_ne_b : x ≠ b := by
      intro hxb
      subst hxb
      exact hb_not_in_ops1 hx
    have hx''' : x ∈ ops₀_first ∨ x ∈ b :: ops₀_last ++ [a] := by
      have hx''_norm : x ∈ ops₀_first ++ (b :: ops₀_last ++ [a]) := by
        simpa [List.append_assoc] using hx''
      exact (List.mem_append).1 hx''_norm
    cases hx''' with
    | inl hmem =>
      have hx_all : x ∈ ops₀_first ++ (ops₀_last ++ [a]) :=
        (List.mem_append).2 (Or.inl hmem)
      simpa [List.append_assoc] using hx_all
    | inr hmem =>
      have hmem' : x = b ∨ x ∈ ops₀_last ++ [a] := by
        simpa using hmem
      cases hmem' with
      | inl hxb => cases hx_ne_b hxb
      | inr hlast =>
        have hx_all : x ∈ ops₀_first ++ (ops₀_last ++ [a]) :=
          (List.mem_append).2 (Or.inr hlast)
        simpa [List.append_assoc] using hx_all

theorem hb_consistent_effect_convergent [MonotoneOperation A (hb := hb) S] (ops₀ ops₁ : List A)
  (h_source₀ : ∀ x, x ∈ ops₀ → MonotoneOperation.StateSource (A := A) (hb := hb) x)
  (h_source₁ : ∀ x, x ∈ ops₁ → MonotoneOperation.StateSource (A := A) (hb := hb) x)
  (h_consistent₀ : hb_consistent hb ops₀)
  (h_consistent₁ : hb_consistent hb ops₁)
  (hclosed₀ : hbClosed hb ops₀)
  (hclosed₁ : hbClosed hb ops₁)
  (h_commutative : concurrent_commutative (hb := hb) ops₀)
  (no_dup₀ : IdNoDup ops₀) (no_dup₁ : IdNoDup ops₁) :
  (∀ a, a ∈ ops₀ ↔ a ∈ ops₁) →
  effect_list ops₀ Operation.init = Except.ok s →
  effect_list ops₁ Operation.init = Except.ok s :=
by
  induction ops₁ using List.reverseRecOn generalizing ops₀ s with
  | nil =>
    intros h_mem hops₀
    have ops₀_eq_nil : ops₀ = [] := by
      cases ops₀ with
      | nil => rfl
      | cons a ops₀ =>
        specialize h_mem a
        simp at h_mem
    grind
  | append_singleton ops₁ b ih =>
    intros h_mem hops₀
    cases List.eq_nil_or_concat' ops₀ with
    | inl h =>
      subst h; simp at h_mem; grind
    | inr h =>
      replace ⟨ ops₀, a, h ⟩ := h; subst h
      by_cases h_eq : a = b
      . -- Case a = b
        simp at hops₀ |-
        have ⟨ u, h_effects_eq, h_effect_b_eq ⟩ := Except.bind_eq_ok_exist hops₀
        rw [←h_eq, ih (ops₀ := ops₀) (s := u)]
        . assumption
        . intro x hx
          exact h_source₀ x (by simp [hx])
        . intro x hx
          exact h_source₁ x (by simp [hx])
        . apply hb_consistent_sublist _ h_consistent₀; grind
        . apply hb_consistent_sublist _ h_consistent₁; grind
        . grind [hbClosed]
        . grind [hbClosed]
        . grind [concurrent_commutative]
        . grind [IdNoDup]
        . grind [IdNoDup]
        . subst h_eq
          intros x
          have h := h_mem x
          simp at h
          grind [IdNoDup]
        . assumption
      . -- Case a ≠ b
        have ⟨ ops₀_first, ops₀_last, h_ops₀_eq ⟩ : ∃ ops₀_first ops₀_last, ops₀ = ops₀_first ++ b :: ops₀_last := by
          have h_a_mem_ops₀ : b ∈ ops₀ := by
            specialize h_mem b
            simp at h_mem
            grind
          rw [List.mem_iff_append] at h_a_mem_ops₀
          assumption
        rw [h_ops₀_eq] at hops₀
        simp at hops₀ |-
        have h_a_concurrent_ops₀_last : ∀ x, x ∈ ops₀_last → hb_concurrent hb x b := by
          intros x h_mem_ops₀_last
          have h : x ∈ ops₁ ∨ x = b := by
              have h : x ∈ ops₀ := by grind
              specialize h_mem x
              grind
          have h_x_b : x ≠ b := by grind [IdNoDup]
          have hnotxltb : ¬ x ≤ b := by
            grind [List.mem_iff_append]
          rw [List.mem_iff_append] at h_mem_ops₀_last
          grind [hb_concurrent]
        subst h_ops₀_eq
        have heq :
          (do let s ← (effect_list ops₀_first Operation.init >>= Operation.effect b); effect_list ops₀_last s)  =
          (do let s ← effect_list ops₀_first Operation.init; effect_list ops₀_last s >>= Operation.effect b) := by
          have h : (do
              let s <- (do
                let s ← effect_list ops₀_first Operation.init >>= Operation.effect b
                effect_list ops₀_last s);
              let s ← Operation.effect a s
              Except.ok s) =
            Except.ok s := by
            simp; assumption
          have ⟨ s', ⟨ h, heq ⟩  ⟩ := Except.bind_eq_ok_exist h
          simp
          have h' := h
          apply hb_concurrent_effect_list_reorder (hb := hb) at h
          . simp at *
            rw [h', ←h]
          . intro x hx
            exact h_source₀ x (by
              simp [List.mem_append, List.append_assoc] at hx ⊢
              tauto)
          . grind [concurrent_commutative]
          . assumption
          . grind [hb_consistent_sublist]
          . grind [hbClosed]
          . grind [IdNoDup]
        replace hops₀ : (do
            do let s ← (do
              let s ← effect_list ops₀_first Operation.init >>= Operation.effect b
              effect_list ops₀_last s)
            let s ← Operation.effect a s
            Except.ok s) =
          Except.ok s := by
          simp; assumption
        rw [heq] at hops₀
        simp at hops₀
        replace heq : (do
          let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
          let s ← Operation.effect b x
          let s ← Operation.effect a s
          Except.ok s) = (do
          let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
          let s ← Operation.effect a x
          let s ← Operation.effect b s
          Except.ok s) := by
          replace hops₀ : (do
            let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
            let s ← Operation.effect b x
            let s ← Operation.effect a s
            Except.ok s) = Except.ok s := by
            simp at *; assumption
          have ⟨ s', ⟨ h, heq ⟩  ⟩ := Except.bind_eq_ok_exist hops₀
          -- have ⟨ s'', h_effects_eq, h_effect_a_eq ⟩ := Except.bind_eq_ok_exist h
          -- rw [h_effects_eq] at hops₀ |-
          have hab : (do
            let s ← Operation.effect b s'
            Operation.effect a s) = Except.ok s := by
            -- unpack the do-notation
            cases hbs : Operation.effect b s' with
            | error err =>
              simp [bind, Except.bind, hbs] at heq
            | ok sb =>
              have ha : Operation.effect a sb = Except.ok s := by
                cases hsa : Operation.effect a sb with
                | error err =>
                  simp [bind, Except.bind, hbs, hsa] at heq
                | ok v =>
                  have hv : v = s := by
                    simpa [bind, Except.bind, hbs, hsa] using heq
                  subst hv
                  simpa [hsa]
              simp [bind, Except.bind, hbs, ha]
          have h_eff : effect_list (ops₀_first ++ ops₀_last) Operation.init = Except.ok s' := by
            simpa [effect_list_append] using h
          have h_closed_prefix : hbClosed hb (ops₀_first ++ ops₀_last) :=
            hbClosed_remove_concurrent (hb := hb) ops₀_first ops₀_last a b hclosed₀ h_a_concurrent_ops₀_last
          have h_stateInv_s' : Operation.StateInv s' := by
            apply effect_list_stateInv (hb := hb) (S := S) (ops := ops₀_first ++ ops₀_last)
            · intro x hx
              exact h_source₀ x (by
                simp [List.mem_append, List.append_assoc] at hx ⊢
                tauto)
            · apply hb_consistent_sublist (hb := hb) h_consistent₀
              grind
            · exact h_closed_prefix
            · grind [IdNoDup]
            · exact h_eff
          have hab_swap : Operation.effect a s' >>= Operation.effect b = Except.ok s := by
            apply h_commutative b a s' s
            · simp
            · simp
            · -- b ∥ a
              have h_not_a_le_b : ¬ a ≤ b := by
                have h := hb_consistent_concurrent (hb := hb) (a := a)
                  (ops₀ := ops₀_first ++ b :: ops₀_last) (ops₁ := []) (by simpa [List.append_assoc] using h_consistent₀)
                  b (by simp)
                exact h
              have h_not_b_le_a : ¬ b ≤ a := by
                have ha_mem : a ∈ ops₁ := by
                  have ha_mem' : a ∈ ops₁ ++ [b] := by
                    have ha_mem_ops₀ : a ∈ ops₀_first ++ b :: ops₀_last ++ [a] := by simp
                    have := (h_mem a).1 (by simpa [List.append_assoc] using ha_mem_ops₀)
                    simpa [List.mem_append, h_eq] using this
                  simpa [List.mem_append, h_eq] using ha_mem'
                have h := hb_consistent_concurrent (hb := hb) (a := b)
                  (ops₀ := ops₁) (ops₁ := []) (by simpa using h_consistent₁) a ha_mem
                exact h
              exact And.intro h_not_b_le_a h_not_a_le_b
            · exact h_stateInv_s'
            · -- isValidState b s'
              refine MonotoneOperation.isValidState_mono (hb := hb) (a := b) (s := s')
                (l := ops₀_first ++ ops₀_last) ?_ ?_ ?_ ?_ h_eff ?_
              · exact h_source₀ b (by simp [List.mem_append, List.append_assoc])
              · intro x hxlt
                have h' := hclosed₀ b x (ops₀_first) (ops₀_last ++ [a]) (by simp [List.append_assoc]) hxlt
                exact (List.mem_append).2 (Or.inl h')
              · apply hb_consistent_sublist _ h_consistent₀
                grind
              · exact h_closed_prefix
              · grind [IdNoDup]
            · -- isValidState a s'
              refine MonotoneOperation.isValidState_mono (hb := hb) (a := a) (s := s')
                (l := ops₀_first ++ ops₀_last) ?_ ?_ ?_ ?_ h_eff ?_
              · exact h_source₀ a (by simp [List.mem_append, List.append_assoc])
              · intro x hxlt
                have h' := hclosed₀ a x (ops₀_first ++ b :: ops₀_last) [] (by simp [List.append_assoc]) hxlt
                -- x ≠ b since b ≤ a would contradict h_not_b_le_a
                have h_not_b_le_a : ¬ b ≤ a := by
                  have ha_mem : a ∈ ops₁ := by
                    have ha_mem' : a ∈ ops₁ ++ [b] := by
                      have ha_mem_ops₀ : a ∈ ops₀_first ++ b :: ops₀_last ++ [a] := by simp
                      have := (h_mem a).1 (by simpa [List.append_assoc] using ha_mem_ops₀)
                      simpa [List.mem_append, h_eq] using this
                    simpa [List.mem_append, h_eq] using ha_mem'
                  have h := hb_consistent_concurrent (hb := hb) (a := b)
                    (ops₀ := ops₁) (ops₁ := []) (by simpa using h_consistent₁) a ha_mem
                  exact h
                have hx_ne_b : x ≠ b := by
                  intro hx_eq
                  subst hx_eq
                  exact h_not_b_le_a (le_of_lt hxlt)
                -- remove the b case from membership
                simp [List.mem_append, hx_ne_b] at h'
                exact (List.mem_append).2 h'
              · apply hb_consistent_sublist _ h_consistent₀
                grind
              · exact h_closed_prefix
              · grind [IdNoDup]
            · exact hab
          -- close the goal using h and hab
          have hab' : (do
            let s ← Operation.effect a s'
            let s ← Operation.effect b s
            Except.ok s) = Except.ok s := by
            cases hba : Operation.effect a s' with
            | error err =>
              simp [bind, Except.bind, hba] at hab_swap
            | ok sa =>
              have hab'' : Operation.effect b sa = Except.ok s := by
                simpa [bind, Except.bind, hba] using hab_swap
              simp [bind, Except.bind, hba, hab'']
          have h_right' : (do
            let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
            let s ← Operation.effect a x
            let s ← Operation.effect b s
            Except.ok s) = Except.ok s := by
            rw [h]
            simpa [Except.ok_bind] using hab'
          calc
            (do
                let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
                let s ← Operation.effect b x
                let s ← Operation.effect a s
                Except.ok s) = Except.ok s := hops₀
            _ = (do
                let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
                let s ← Operation.effect a x
                let s ← Operation.effect b s
                Except.ok s) := h_right'.symm
        simp at heq
        rw [heq] at hops₀
        replace heq : (do
          let x ← effect_list ops₀_first Operation.init
          let x ← effect_list ops₀_last x
          let s ← Operation.effect a x
          let s ← Operation.effect b s
          Except.ok s) = (do
          let x ← effect_list ops₁ Operation.init
          let s ← Operation.effect b x
          Except.ok s) := by
          have h_left_eq :
              (do
                  let x ← effect_list ops₀_first Operation.init
                  let x ← effect_list ops₀_last x
                  let s ← Operation.effect a x
                  let s ← Operation.effect b s
                  Except.ok s)
                =
                (do
                  let s ← effect_list (ops₀_first ++ ops₀_last ++ [a]) Operation.init
                  let s ← Operation.effect b s
                  Except.ok s) := by
            simp; rfl
          have hops₀' :
              (do
                  let s ← effect_list (ops₀_first ++ ops₀_last ++ [a]) Operation.init
                  let s ← Operation.effect b s
                  Except.ok s) = Except.ok s := by
            simpa [h_left_eq] using hops₀
          have ⟨ s', ⟨ h_eff, h_b ⟩  ⟩ := Except.bind_eq_ok_exist hops₀'
          have h_closed_prefix : hbClosed hb (ops₀_first ++ ops₀_last) :=
            hbClosed_remove_concurrent (hb := hb) ops₀_first ops₀_last a b hclosed₀ h_a_concurrent_ops₀_last
          have h_all_lt : ∀ x < a, x ∈ ops₀_first ++ ops₀_last := by
            intro x hxlt
            have hx_mem : x ∈ ops₀_first ++ b :: ops₀_last := by
              have hx_mem' :=
                hclosed₀ a x (ops₀_first ++ b :: ops₀_last) [] (by simp [List.append_assoc]) hxlt
              simpa using hx_mem'
            -- x ≠ b since b ≤ a would contradict consistency
            have h_not_b_le_a : ¬ b ≤ a := by
              have ha_mem : a ∈ ops₁ := by
                have ha_mem' : a ∈ ops₁ ++ [b] := by
                  have ha_mem_ops₀ : a ∈ ops₀_first ++ b :: ops₀_last ++ [a] := by simp
                  have := (h_mem a).1 (by simpa [List.append_assoc] using ha_mem_ops₀)
                  simpa [List.mem_append, h_eq] using this
                simpa [List.mem_append, h_eq] using ha_mem'
              have h := hb_consistent_concurrent (hb := hb) (a := b)
                (ops₀ := ops₁) (ops₁ := []) (by simpa using h_consistent₁) a ha_mem
              exact h
            have hx_ne_b : x ≠ b := by
              intro hx_eq
              subst hx_eq
              exact h_not_b_le_a (le_of_lt hxlt)
            have hx_mem' : x ∈ ops₀_first ∨ x ∈ b :: ops₀_last := by
              simpa [List.mem_append] using hx_mem
            cases hx_mem' with
            | inl hmem =>
              exact (List.mem_append).2 (Or.inl hmem)
            | inr hmem =>
              have hx_mem'' : x = b ∨ x ∈ ops₀_last := by
                simpa using hmem
              cases hx_mem'' with
              | inl hxb => cases hx_ne_b hxb
              | inr hlast => exact (List.mem_append).2 (Or.inr hlast)
          have h_closed_full : hbClosed hb (ops₀_first ++ ops₀_last ++ [a]) := by
            have h_closed : hbClosed hb ((ops₀_first ++ ops₀_last) ++ [a]) :=
              hbClosed_append_singleton_of_all_lt (hb := hb) h_closed_prefix h_all_lt
            simpa [List.append_assoc] using h_closed
          have h_ops1 :
              effect_list ops₁ Operation.init = Except.ok s' :=
            ih (ops₀ := ops₀_first ++ ops₀_last ++ [a]) (s := s')
              (by
                intro x hx
                exact h_source₀ x (by
                  simp [List.mem_append, List.append_assoc] at hx ⊢
                  tauto))
              (by
                intro x hx
                exact h_source₁ x (by simp [hx]))
              (by grind [hb_consistent_sublist])
              (by grind [hb_consistent_sublist])
              h_closed_full
              (by grind [hbClosed])
              (by grind [concurrent_commutative])
              (by grind [IdNoDup])
              (by grind [IdNoDup])
              (by
                simpa using
                  (mem_ops0_prefix_iff_ops1 (ops₀_first := ops₀_first) (ops₀_last := ops₀_last)
                    (ops₁ := ops₁) (a := a) (b := b) no_dup₀ no_dup₁ h_mem))
              h_eff
          have h_right :
              (do
                  let x ← effect_list ops₁ Operation.init
                  let s ← Operation.effect b x
                  Except.ok s) = Except.ok s := by
            simpa [Except.ok_bind, h_ops1] using h_b
          have h_left :
              (do
                  let x ← effect_list ops₀_first Operation.init
                  let x ← effect_list ops₀_last x
                  let s ← Operation.effect a x
                  let s ← Operation.effect b s
                  Except.ok s) = Except.ok s :=
            h_left_eq.trans hops₀'
          exact h_left.trans h_right.symm
        rw [heq] at hops₀
        rw [<-hops₀]
end commutativity
