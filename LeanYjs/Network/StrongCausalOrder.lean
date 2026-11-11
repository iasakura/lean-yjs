import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Use
import Mathlib.Tactic.CongrExclamation
import Mathlib.Data.List.Induction

import LeanYjs.ListLemmas
import LeanYjs.ExceptLemmas
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

/-- Every element of a sublist is an element of the list. -/
theorem List.sublist_mem {A : Type} {l₁ l₂ : List A} (h_sublist : l₁ <+ l₂) {a : A} :
  a ∈ l₁ → a ∈ l₂ :=
  fun h_mem => h_sublist.subset h_mem

omit [DecidableEq A] in
/-- Every sublist of an hb-consistent list is hb-consistent. -/
theorem hb_consistent_sublist {ops₀ ops₁ : List A} :
  hb_consistent hb ops₀ →
  ops₁ <+ ops₀ →
  hb_consistent hb ops₁ := by
  intro h_consistent h_sublist
  induction h_sublist with
  | slnil => exact h_consistent
  | cons _ _ ih =>
    cases h_consistent with
    | cons _ _ h_tail _ => exact ih h_tail
  | cons₂ x h_sublist ih =>
    cases h_consistent with
    | cons _ _ h_tail h_no_le =>
      exact hb_consistent.cons x _ (ih h_tail) fun b h_mem => h_no_le b (h_sublist.subset h_mem)

omit [DecidableEq A] in
/-- Dropping the first element of an hb-consistent list keeps it hb-consistent. -/
lemma hb_consistent_tail (a : A) (ops : List A) :
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

/-- Running `ops ++ [a]` from `s₀` reaches `s` exactly when running `ops` reaches some state `u`
from which `a` reaches `s`. -/
theorem effect_list_append_singleton_eq_ok [Operation A] {ops : List A} {a : A}
  {s₀ s : Operation.State A} :
  effect_list (ops ++ [a]) s₀ = Except.ok s ↔
    ∃ u, effect_list ops s₀ = Except.ok u ∧ Operation.effect a u = Except.ok s := by
  simp [Except.bind_eq_ok_iff]

class ValidatableOperation (A : Type) [Operation A] where
  isValidState : A → Operation.State A → Prop
  StateInv : Operation.State A → Prop := fun _ => True
  stateInv_init : StateInv (Operation.init (A := A))
  stateInv_effect : ∀ (op : A) (s s' : Operation.State A),
    StateInv s →
    isValidState op s →
    Operation.effect op s = Except.ok s' →
    StateInv s'

class CausallyValidatableOperation
  (A : Type) [DecidableEq A] {S : Type} [DecidableEq S]
  [Operation A] [ValidatableOperation A] [WithId A S]
  (hb : CausalOrder A) (StateSource : A → Prop) : Prop where
  isValidState_of_history :
    ∀ {a : A} {s : Operation.State A} {l : List A},
      StateSource a →
      (∀ x < a, x ∈ l) →
      hb_consistent hb l →
      hbClosed hb l →
      effect_list l (Operation.init (A := A)) = Except.ok s →
      IdNoDup l →
      ValidatableOperation.isValidState a s
end effect

section commutativity

variable {A : Type} [DecidableEq A] {S : Type} [DecidableEq S] {hb : CausalOrder A}
variable [WithId A S] [Operation A] [ValidatableOperation A]

def concurrent_commutative (list : List A) : Prop :=
  ∀ a b (s s' : Operation.State A), a ∈ list → b ∈ list → hb_concurrent hb a b →
    ValidatableOperation.StateInv s →
    ValidatableOperation.isValidState a s →
    ValidatableOperation.isValidState b s →
    (Operation.effect a s >>= Operation.effect b) = Except.ok s' → (Operation.effect b s >>= Operation.effect a) = Except.ok s'

/-- A successful bind consists of a successful first step followed by a successful continuation. -/
theorem Except.bind_eq_ok_exist' {α β : Type} {e : Except α β} {f : β → Except α β'} {v : β'} :
  e >>= f = Except.ok v →
  ∃ u : β, e = Except.ok u ∧ f u = Except.ok v :=
  Except.bind_eq_ok_iff.1

/-- Executing a history of source operations that is hb-consistent, hb-closed and duplicate-free
from the initial state yields a state satisfying `StateInv`. -/
theorem effect_list_stateInv (StateSource : A → Prop)
  [CausallyValidatableOperation (A := A) (S := S) (hb := hb) StateSource] :
  ∀ {ops : List A} {s : Operation.State A},
    (∀ op, op ∈ ops → StateSource op) →
    hb_consistent hb ops →
    hbClosed hb ops →
    IdNoDup ops →
    effect_list ops Operation.init = Except.ok s →
    ValidatableOperation.StateInv s := by
  intro ops s h_source h_consistent h_closed h_no_dup h_effect
  induction ops using List.reverseRecOn generalizing s with
  | nil =>
    cases h_effect
    exact ValidatableOperation.stateInv_init (A := A)
  | append_singleton ops a ih =>
    have h_consistent_ops : hb_consistent hb ops :=
      hb_consistent_sublist _ h_consistent (List.sublist_append_left _ _)
    have h_closed_ops : hbClosed hb ops := by grind [hbClosed]
    have h_no_dup_ops : IdNoDup ops := by grind [IdNoDup]
    obtain ⟨s_prev, h_prefix, h_last⟩ := effect_list_append_singleton_eq_ok.1 h_effect
    have h_stateInv_prev : ValidatableOperation.StateInv s_prev :=
      ih (fun op hop => h_source op (by simp [hop]))
        h_consistent_ops h_closed_ops h_no_dup_ops h_prefix
    have h_valid_a : ValidatableOperation.isValidState a s_prev :=
      CausallyValidatableOperation.isValidState_of_history
        (A := A) (S := S) (hb := hb) (StateSource := StateSource)
        (h_source a (by simp)) (fun x hx => h_closed a x ops [] rfl hx)
        h_consistent_ops h_closed_ops h_prefix h_no_dup_ops
    exact ValidatableOperation.stateInv_effect a s_prev s h_stateInv_prev h_valid_a h_last

/-- In an hb-consistent list, an operation is never causally below an operation preceding it. -/
@[grind .] theorem hb_consistent_concurrent (a : A) (ops₀ ops₁ : List A) :
  hb_consistent hb (ops₀ ++ a :: ops₁) →
  ∀ x, x ∈ ops₀ → ¬a ≤ x := by
  intro h_consistent x h_mem
  induction ops₀ with
  | nil => simp at h_mem
  | cons y ys ih =>
    cases h_consistent with
    | cons _ _ h_tail h_no_le =>
      rcases List.mem_cons.1 h_mem with rfl | h_mem
      · exact h_no_le a (by simp)
      · exact ih h_tail h_mem

omit [DecidableEq A] [Operation A] [ValidatableOperation A] in
/-- In an hb-consistent list, no operation is causally below an operation following it. -/
theorem hb_consistent_not_le_of_later (a : A) (ops₀ ops₁ : List A) :
  hb_consistent hb (ops₀ ++ a :: ops₁) →
  ∀ x, x ∈ ops₁ → ¬ x ≤ a := by
  intro h_consistent
  cases hb_consistent_sublist _ h_consistent (List.sublist_append_right _ _) with
  | cons _ _ _ h_no_le => exact h_no_le

/-- A successful bind consists of a successful first step followed by a successful continuation. -/
theorem Except.bind_eq_ok_exist {α β : Type} {e : Except α β} {f : β → Except α β'} {v : β'} :
  e >>= f = Except.ok v →
  ∃ u : β, e = Except.ok u ∧ f u = Except.ok v :=
  Except.bind_eq_ok_iff.1

/-- Swapping two adjacent concurrent operations preserves hb-consistency. -/
theorem hb_consistent_swap (ops₀ ops₁ : List A) (a b : A) :
  hb_consistent hb (ops₀ ++ a :: b :: ops₁) →
  hb_concurrent hb b a →
  hb_consistent hb (ops₀ ++ b :: a :: ops₁) := by
  intro h_consistent h_concurrent
  induction ops₀ with
  | nil =>
    cases h_consistent with
    | cons _ _ h_tail h_no_le_a =>
      cases h_tail with
      | cons _ _ h_ops₁ h_no_le_b =>
        refine hb_consistent.cons b (a :: ops₁) (hb_consistent.cons a ops₁ h_ops₁ ?_) ?_
        · exact fun x hx => h_no_le_a x (by simp [hx])
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact h_concurrent.2
          · exact h_no_le_b x hx
  | cons x xs ih =>
    rw [List.cons_append] at h_consistent ⊢
    cases h_consistent with
    | cons _ _ h_tail h_no_le_x =>
      refine hb_consistent.cons x _ (ih h_tail) fun y hy => h_no_le_x y ?_
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      tauto

/-- Executing `a` before a run of operations that are all concurrent with `a` reaches the same
state as executing `a` after them. -/
theorem hb_concurrent_effect_list_reorder (StateSource : A → Prop)
  [CausallyValidatableOperation (A := A) (S := S) (hb := hb) StateSource]
  {s : Operation.State A} :
  (∀ x, x ∈ (ops₀ ++ a :: ops₁) → StateSource x) →
  concurrent_commutative (hb := hb) (ops₀ ++ a :: ops₁) →
  (∀ x ∈ ops₁, hb_concurrent hb x a) →
  hb_consistent hb (ops₀ ++ a :: ops₁) →
  hbClosed hb (ops₀ ++ a :: ops₁) →
  IdNoDup (ops₀ ++ a :: ops₁) →
  (do let s <- effect_list ops₀ Operation.init >>= Operation.effect a; effect_list ops₁ s) = Except.ok s →
  (do let s <- effect_list ops₀ Operation.init; effect_list ops₁ s) >>= Operation.effect a = Except.ok s := by
  induction ops₁ generalizing ops₀ with
  | nil =>
    intro _ _ _ _ _ _ heq
    simpa [effect_list] using heq
  | cons b ops₁ ih =>
    intro h_source h_comm h_concurrent h_consistent h_closed h_no_dup heq
    -- The run reaches `u` after `ops₀`, `sa` after `a`, `sb` after `b`, and `s` after `ops₁`.
    obtain ⟨u, h_u, sa, h_sa, sb, h_sb, h_rest⟩ :
        ∃ u, effect_list ops₀ Operation.init = Except.ok u ∧
          ∃ sa, Operation.effect a u = Except.ok sa ∧
            ∃ sb, Operation.effect b sa = Except.ok sb ∧ effect_list ops₁ sb = Except.ok s := by
      simpa [Except.bind_eq_ok_iff] using heq
    have h_source₀ : ∀ x ∈ ops₀, StateSource x := fun x hx => h_source x (by simp [hx])
    have h_consistent₀ : hb_consistent hb ops₀ :=
      hb_consistent_sublist _ h_consistent (List.sublist_append_left _ _)
    have h_closed₀ : hbClosed hb ops₀ := by grind [hbClosed]
    have h_no_dup₀ : IdNoDup ops₀ := by grind [IdNoDup]
    have h_b_concurrent_a : hb_concurrent hb b a := h_concurrent b (by simp)
    -- Both `a` and `b` are valid at `u`, so they can be swapped there.
    have h_stateInv_u : ValidatableOperation.StateInv u :=
      effect_list_stateInv (hb := hb) (S := S) StateSource
        h_source₀ h_consistent₀ h_closed₀ h_no_dup₀ h_u
    have h_valid_a : ValidatableOperation.isValidState a u :=
      CausallyValidatableOperation.isValidState_of_history
        (A := A) (S := S) (hb := hb) (StateSource := StateSource)
        (h_source a (by simp)) (fun x hx => h_closed a x ops₀ (b :: ops₁) rfl hx)
        h_consistent₀ h_closed₀ h_u h_no_dup₀
    have h_valid_b : ValidatableOperation.isValidState b u := by
      refine CausallyValidatableOperation.isValidState_of_history
        (A := A) (S := S) (hb := hb) (StateSource := StateSource)
        (h_source b (by simp)) (fun x hx => ?_) h_consistent₀ h_closed₀ h_u h_no_dup₀
      have hx_mem : x ∈ ops₀ ++ [a] := h_closed b x (ops₀ ++ [a]) ops₁ (by simp) hx
      have hx_ne_a : x ≠ a := by
        rintro rfl
        exact h_b_concurrent_a.2 (le_of_lt hx)
      simpa [hx_ne_a] using hx_mem
    have h_ba : Operation.effect b u >>= Operation.effect a = Except.ok sb :=
      h_comm a b u sb (by simp) (by simp) ((hb_concurrent_symm hb).2 h_b_concurrent_a)
        h_stateInv_u h_valid_a h_valid_b (Except.bind_eq_ok_iff.2 ⟨sa, h_sa, h_sb⟩)
    obtain ⟨sb', h_sb', h_sa'⟩ := Except.bind_eq_ok_iff.1 h_ba
    -- With `b` now before `a`, the induction hypothesis moves `a` past `ops₁`.
    have h_ih := ih (ops₀ := ops₀ ++ [b])
      (fun x hx => h_source x (by simp at hx ⊢; tauto))
      (by grind [concurrent_commutative])
      (fun x hx => h_concurrent x (by simp [hx]))
      (by simpa using hb_consistent_swap ops₀ ops₁ a b h_consistent h_b_concurrent_a)
      (by simpa using hbClosed_swap hb ops₀ ops₁ a b h_closed h_b_concurrent_a)
      (by grind [IdNoDup])
      (by
        rw [effect_list_append_singleton_eq_ok.2 ⟨u, h_u, h_sb'⟩, Except.ok_bind, h_sa',
          Except.ok_bind]
        exact h_rest)
    simpa [Except.bind_eq_ok_iff] using h_ih

/-- Removing `b` from `ops₀_first ++ b :: ops₀_last ++ [a]` and from `ops₁ ++ [b]` leaves two lists
with the same elements. -/
theorem mem_ops0_prefix_iff_ops1
  (ops₀_first ops₀_last ops₁ : List A) (a b : A)
  (no_dup₀ : IdNoDup (ops₀_first ++ b :: ops₀_last ++ [a]))
  (no_dup₁ : IdNoDup (ops₁ ++ [b]))
  (h_mem : ∀ x, x ∈ ops₀_first ++ b :: ops₀_last ++ [a] ↔ x ∈ ops₁ ++ [b]) :
  ∀ x, x ∈ ops₀_first ++ ops₀_last ++ [a] ↔ x ∈ ops₁ := by
  intro x
  have h_b_not_in_ops₁ : b ∉ ops₁ := by grind [IdNoDup]
  have h_b_not_in_ops₀ : b ∉ ops₀_first ++ ops₀_last ++ [a] := by grind [IdNoDup]
  have := h_mem x
  simp only [List.mem_append, List.mem_cons, not_or] at *
  grind

/-- Two hb-consistent, hb-closed, duplicate-free histories over the same operations, in which
concurrent operations commute, lead from the initial state to the same state. -/
theorem hb_consistent_effect_convergent (StateSource : A → Prop)
  [CausallyValidatableOperation (A := A) (S := S) (hb := hb) StateSource]
  (ops₀ ops₁ : List A) (s : Operation.State A)
  (h_source₀ : ∀ x, x ∈ ops₀ → StateSource x)
  (h_source₁ : ∀ x, x ∈ ops₁ → StateSource x)
  (h_consistent₀ : hb_consistent hb ops₀)
  (h_consistent₁ : hb_consistent hb ops₁)
  (hclosed₀ : hbClosed hb ops₀)
  (hclosed₁ : hbClosed hb ops₁)
  (h_commutative : concurrent_commutative (hb := hb) ops₀)
  (no_dup₀ : IdNoDup ops₀) (no_dup₁ : IdNoDup ops₁) :
  (∀ a, a ∈ ops₀ ↔ a ∈ ops₁) →
  effect_list ops₀ Operation.init = Except.ok s →
  effect_list ops₁ Operation.init = Except.ok s := by
  induction ops₁ using List.reverseRecOn generalizing ops₀ s with
  | nil =>
    intro h_mem hops₀
    obtain rfl : ops₀ = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun x hx => by simpa using (h_mem x).1 hx
    exact hops₀
  | append_singleton ops₁ b ih =>
    intro h_mem hops₀
    -- `b ∈ ops₀`, so `ops₀` ends with some operation `a`.
    obtain ⟨ops₀, a, rfl⟩ : ∃ ops₀' a, ops₀ = ops₀' ++ [a] := by
      rcases List.eq_nil_or_concat' ops₀ with rfl | h
      · simpa using (h_mem b).2 (by simp)
      · exact h
    by_cases h_eq : a = b
    · -- Both histories end with the same operation; drop it and apply the induction hypothesis.
      subst h_eq
      obtain ⟨u, h_prefix, h_last⟩ := effect_list_append_singleton_eq_ok.1 hops₀
      refine effect_list_append_singleton_eq_ok.2 ⟨u, ?_, h_last⟩
      refine ih ops₀ u
        (fun x hx => h_source₀ x (by simp [hx])) (fun x hx => h_source₁ x (by simp [hx]))
        (hb_consistent_sublist _ h_consistent₀ (List.sublist_append_left _ _))
        (hb_consistent_sublist _ h_consistent₁ (List.sublist_append_left _ _))
        (by grind [hbClosed]) (by grind [hbClosed]) (by grind [concurrent_commutative])
        (by grind [IdNoDup]) (by grind [IdNoDup]) ?_ h_prefix
      -- The dropped operation occurs in neither remaining list, so their memberships agree.
      intro x
      have := h_mem x
      simp at this
      grind [IdNoDup]
    · -- `b` occurs strictly inside `ops₀`: `ops₀ = ops₀_first ++ b :: ops₀_last ++ [a]`.
      obtain ⟨ops₀_first, ops₀_last, rfl⟩ : ∃ l₁ l₂, ops₀ = l₁ ++ b :: l₂ := by
        have h_b_mem : b ∈ ops₀ := by
          have := (h_mem b).2 (by simp)
          simpa [Ne.symm h_eq] using this
        exact List.mem_iff_append.1 h_b_mem
      -- Every operation after `b` in `ops₀` also occurs in `ops₁`, hence is concurrent with `b`.
      have h_after_b_concurrent : ∀ x ∈ ops₀_last ++ [a], hb_concurrent hb x b := by
        intro x hx
        have hx_ne_b : x ≠ b := by grind [IdNoDup]
        have hx_ops₁ : x ∈ ops₁ := by
          have := (h_mem x).1 (by simp at hx ⊢; tauto)
          simpa [hx_ne_b] using this
        exact ⟨hb_consistent_not_le_of_later b _ _ (by simpa using h_consistent₀) x hx,
          hb_consistent_concurrent b ops₁ [] h_consistent₁ x hx_ops₁⟩
      have h_b_not_le_a : ¬ b ≤ a := (h_after_b_concurrent a (by simp)).2
      -- Moving `b` to the end of `ops₀` does not change the resulting state.
      have h_reordered :
          effect_list (ops₀_first ++ ops₀_last ++ [a]) Operation.init >>= Operation.effect b =
            Except.ok s := by
        have := hb_concurrent_effect_list_reorder (hb := hb) (S := S) StateSource
          (ops₀ := ops₀_first) (a := b) (ops₁ := ops₀_last ++ [a])
          (by simpa using h_source₀) (by simpa using h_commutative) h_after_b_concurrent
          (by simpa using h_consistent₀) (by simpa using hclosed₀) (by simpa using no_dup₀)
          (by simpa using hops₀)
        rw [List.append_assoc, effect_list_append]
        exact this
      obtain ⟨u, h_prefix, h_b⟩ := Except.bind_eq_ok_iff.1 h_reordered
      -- Removing `b` from `ops₀` keeps the history hb-closed: nothing below `a` is `b`.
      have h_closed' : hbClosed hb (ops₀_first ++ ops₀_last ++ [a]) := by
        have h_closed_removed : hbClosed hb (ops₀_first ++ ops₀_last) :=
          hbClosed_remove_concurrent hb _ _ a b hclosed₀
            fun x hx => h_after_b_concurrent x (by simp [hx])
        refine hbClosed_append_singleton_of_all_lt hb h_closed_removed fun x hx => ?_
        have hx_mem : x ∈ ops₀_first ++ b :: ops₀_last := hclosed₀ a x _ [] rfl hx
        have hx_ne_b : x ≠ b := by
          rintro rfl
          exact h_b_not_le_a (le_of_lt hx)
        simpa [hx_ne_b] using hx_mem
      -- The induction hypothesis applies to `ops₀` without `b`, and `ops₁`.
      refine effect_list_append_singleton_eq_ok.2 ⟨u, ?_, h_b⟩
      exact ih (ops₀_first ++ ops₀_last ++ [a]) u
        (fun x hx => h_source₀ x (by simp at hx ⊢; tauto)) (fun x hx => h_source₁ x (by simp [hx]))
        (hb_consistent_sublist _ h_consistent₀ (by grind))
        (hb_consistent_sublist _ h_consistent₁ (List.sublist_append_left _ _))
        h_closed' (by grind [hbClosed]) (by grind [concurrent_commutative])
        (by grind [IdNoDup]) (by grind [IdNoDup])
        (mem_ops0_prefix_iff_ops1 _ _ _ a b no_dup₀ no_dup₁ h_mem) h_prefix
end commutativity
