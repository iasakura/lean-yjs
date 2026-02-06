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

def hbClosed (ops : List A) : Prop :=
  ∀a b l₁ l₂, ops = l₁ ++ a :: l₂ → b < a → b ∈ l₁

end hb_concurrent

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

class MonotoneOperation (A : Type) [hb : CausalOrder A] (S : outParam Type) [DecidableEq S] [WithId A S] [Operation A] extends Operation A where
  -- TODO: is this enough to strong assumption for yjs?
  isValidState_mono : ∀ {l : List A},
    (∀x < a, x ∈ l) →
    hb_consistent hb l →
    hbClosed hb l →
    l.foldl (fun s op => s >>= effect op) (Except.ok init) = Except.ok s →
    IdNoDup l →
    isValidState a s

variable {A : Type} {S : Type} [DecidableEq S] {hb : CausalOrder A}
variable [WithId A S]  [Operation A]

abbrev Effect := Operation.State A → Except (Operation.Error A) (Operation.State A)

def effect (op : A) : Effect (A := A) :=
  Operation.effect op

def effect_comp (op1 op2 : Effect (A := A)) : Effect (A := A) := fun s => op1 s >>= op2

theorem effect_comp_assoc (op1 op2 op3 : Effect (A := A)) :
  effect_comp (effect_comp op1 op2) op3 = effect_comp op1 (effect_comp op2 op3) := by
  funext s
  simp [effect_comp]
  unfold effect_comp
  simp
end effect

local infix:99 " ▷ " => effect_comp

section commutativity

variable {A : Type} {S : Type} [DecidableEq S] {hb : CausalOrder A}
variable [WithId A S]  [Operation A]

def concurrent_commutative (list : List A) : Prop :=
  ∀ a b (s s' : Operation.State A), a ∈ list → b ∈ list → hb_concurrent hb a b →
    Operation.isValidState a s →
    Operation.isValidState b s →
    (effect a s >>= effect b) = Except.ok s' → (effect b s >>= effect a) = Except.ok s'

theorem hb_consistent_concurrent (a : A) (ops₀ ops₁ : List A) :
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

def effect_list (ops : List A) (s : Operation.State A) :=
  foldlM (fun s op => effect op s) s ops

@[simp, grind =] theorem effect_list_nil (s : Operation.State A) :
  effect_list [] s = Except.ok s := by rfl

@[simp, grind =] theorem effect_list_cons (a : A) (ops : List A)
  (s : Operation.State A) :
  effect_list (a :: ops) s = (do let s <- effect a s; effect_list ops s) := by rfl

@[simp, grind =] theorem effect_list_append (ops₀ ops₁ : List A)
  (s : Operation.State A) :
  effect_list (ops₀ ++ ops₁) s = (do let s <- effect_list ops₀ s; effect_list ops₁ s) := by
  induction ops₀ with
  | nil =>
    simp [effect_list]
  | cons a ops₀ ih =>
    simp [effect_list]

theorem Except.ok_bind {α β ε : Type} (x : α) (f : α -> Except β ε) :
  (do
    let x <- Except.ok x
    f x) = f x := by eq_refl

theorem hb_concurrent_foldr :
  concurrent_commutative (hb := hb) (ops₀ ++ a :: ops₁) →
  (∀ x ∈ ops₁, hb_concurrent hb x a) →
  hb_consistent hb (ops₀ ++ a :: ops₁) →
  hbClosed hb (ops₀ ++ a :: ops₁) →
  IdNoDup (ops₀ ++ a :: ops₁) →
  (do let s <- effect_list ops₀ Operation.init >>= effect a; effect_list ops₁ s) = Except.ok s →
  (do let s <- effect_list ops₀ Operation.init; effect_list ops₁ s) >>= effect a = Except.ok s := by
  induction ops₁ generalizing ops₀ with
  | nil =>
    simp [effect_list]
  | cons b ops₁ ih =>
    intro h_comm h_concurrent h_consistent h_closed h_no_dup heq
    simp at *
    have ⟨ s', h ⟩ : ∃ s, (effect_list ops₀ Operation.init >>= fun x => effect a x >>= effect b) = Except.ok s := by
      have h : (do
        let s <- (do
          let x ← effect_list ops₀ Operation.init
          let s ← effect a x
          effect b s)
        effect_list ops₁ s) = Except.ok s := by
        simp; assumption
      grind [Except.bind_eq_ok_exist]
    obtain ⟨ u, h_effects_eq, h_effect_b_eq ⟩ := Except.bind_eq_ok_exist h
    have hba : (effect b u >>= effect a) = Except.ok s' := by
      apply h_comm a b u s'
      . simp
      . simp
      . sorry
      . sorry
      . sorry
      . assumption
    have ⟨ sb, h_sb ⟩ : ∃ sb, effect b u = Except.ok sb := by
      apply Except.bind_eq_ok_exist at hba
      grind
    rw [h_effects_eq] at heq |-
    rw [Except.ok_bind, ←bind_assoc, h_effect_b_eq, ←hba] at heq
    simp at heq
    have heq' : (do
      let x ← effect b u
      let s ← effect a x
      effect_list ops₁ s) =
    (do
      let s ← effect_list (ops₀ ++ [b]) Operation.init
      let s <- effect a s
      effect_list ops₁ s) :=
      by
      simp
      rw [h_effects_eq]; rfl
    rw [heq'] at heq
    apply ih at heq
    . simp at heq
      rw [h_effects_eq] at heq
      assumption
    . sorry
    . grind
    . sorry
    . sorry
    . sorry

theorem effect_comp_apply {op1 op2 : Effect (A := A)} {s : Operation.State A} :
  effect_comp op1 op2 s = op1 s >>= op2 := by
  rfl

theorem hb_consistent_effect_convergent (ops₀ ops₁ : List A)
  (h_consistent₀ : hb_consistent hb ops₀)
  (h_consistent₁ : hb_consistent hb ops₁)
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
        . apply hb_consistent_sublist _ h_consistent₀; grind
        . apply hb_consistent_sublist _ h_consistent₁; grind
        . grind [concurrent_commutative]
        . grind [IdNoDup]
        . grind [IdNoDup]
        . subst h_eq
          intros x
          have h := h_mem x
          simp at h
          sorry
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
          sorry
          -- intros x h_mem_ops₀_last
          -- constructor
          -- . cases h_consistent₀ with
          --   | cons _ _ h_consistent_tail h_no_lt =>
          --     apply h_no_lt
          --     have h_x_in_ops1 : x ∈ b :: ops₁ := by
          --       rw [h_ops₁_eq]
          --       rw [<-List.cons_append]
          --       apply List.mem_append_left
          --       assumption
          --     have x_neq_a : x ≠ a := by
          --       rw [h_ops₁_eq] at no_dup₁
          --       have h_eq' : (b :: (ops₁_first ++ a :: ops₁_last)) = ((b :: ops₁_first) ++ a :: ops₁_last) := by
          --         simp
          --       rw [h_eq'] at no_dup₁
          --       rw [List.nodup_append] at no_dup₁
          --       obtain ⟨ _, _, h_not_a_mem ⟩ := no_dup₁
          --       apply h_not_a_mem
          --       . assumption
          --       . simp
          --     rw [←h_mem] at h_x_in_ops1
          --     simp at h_x_in_ops1
          --     cases h_x_in_ops1 with
          --     | inl h_eq' =>
          --       contradiction
          --     | inr h_mem' =>
          --       assumption
          -- . apply hb_consistent_concurrent hb a (b :: ops₁_first) ops₁_last
          --   . rw [h_ops₁_eq] at h_consistent₁
          --     assumption
          --   . assumption
        subst h_ops₀_eq
        have heq :
          (do let s ← (effect_list ops₀_first Operation.init >>= effect b); effect_list ops₀_last s)  =
          (do let s ← effect_list ops₀_first Operation.init; effect_list ops₀_last s >>= effect b) := by
          have h : (do
              let s <- (do
                let s ← effect_list ops₀_first Operation.init >>= effect b
                effect_list ops₀_last s);
              let s ← effect a s
              Except.ok s) =
            Except.ok s := by
            simp; assumption
          have ⟨ s', ⟨ h, heq ⟩  ⟩ := Except.bind_eq_ok_exist h
          simp
          have h' := h
          apply hb_concurrent_foldr (hb := hb) at h
          . simp at *
            rw [h', ←h]
          . sorry
          . sorry
          . sorry
          . sorry
          . sorry
        replace hops₀ : (do
            do let s ← (do
              let s ← effect_list ops₀_first Operation.init >>= effect b
              effect_list ops₀_last s)
            let s ← effect a s
            Except.ok s) =
          Except.ok s := by
          simp; assumption
        rw [heq] at hops₀
        simp at hops₀
        replace heq : (do
          let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
          let s ← effect b x
          let s ← effect a s
          Except.ok s) = (do
          let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
          let s ← effect a x
          let s ← effect b s
          Except.ok s) := by
          replace hops₀ : (do
            let x ← effect_list ops₀_first Operation.init >>= effect_list ops₀_last
            let s ← effect b x
            let s ← effect a s
            Except.ok s) = Except.ok s := by
            simp at *; assumption
          have ⟨ s', ⟨ h, heq ⟩  ⟩ := Except.bind_eq_ok_exist hops₀
          -- have ⟨ s'', h_effects_eq, h_effect_a_eq ⟩ := Except.bind_eq_ok_exist h
          -- rw [h_effects_eq] at hops₀ |-
          rw [hops₀]
          have hab : (do
            let s ← effect b s'
            effect a s) = Except.ok s := by
            sorry
          apply h_commutative b a at hab
          . sorry
          . simp
          . simp
          . sorry
          . sorry
          . sorry
        simp at heq
        rw [heq] at hops₀
        replace heq : (do
          let x ← effect_list ops₀_first Operation.init
          let x ← effect_list ops₀_last x
          let s ← effect a x
          let s ← effect b s
          Except.ok s) = (do
          let x ← effect_list ops₁ Operation.init
          let s ← effect b x
          Except.ok s) := by
          have heq :
            (do
              let x ← effect_list ops₀_first Operation.init
              let x ← effect_list ops₀_last x
              let s ← effect a x
              let s ← effect b s
              Except.ok s)
            = (do
              let s ← effect_list (ops₀_first ++ ops₀_last ++ [a]) Operation.init
              let s ← effect b s
              Except.ok s) := by
              simp; rfl
          rw [heq] at hops₀
          have ⟨ s', ⟨ h, heq ⟩  ⟩ := Except.bind_eq_ok_exist hops₀
          have h := ih (ops₀ := ops₀_first ++ ops₀_last ++ [a]) (s := s') (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
            (by sorry) (by simp; sorry)
          have ⟨ s', ⟨ h, heq ⟩  ⟩ := Except.bind_eq_ok_exist hops₀
          grind
        rw [heq] at hops₀
        rw [<-hops₀]
        -- Here, we have ops₁ = ops₁_first ++ a :: ops₁_last and a || ops₁_first
        -- have h_concurrent : concurrent_commutative (ops₀_first ++ a :: ops₀_last) := by
        --   intros c d h_c_mem h_d_mem h_concurrent
        --   simp at h_c_mem h_d_mem
        --   apply h_commutative c d _ _ h_concurrent
        --   . rw [h_mem]; simp
        --     right; assumption
        --   . rw [h_mem]; simp
        --     right; assumption
        -- have h_a_b_concurrent : hb_concurrent hb a b := by
        --   rw [hb_concurrent_symm]
        --   apply h_a_concurrent_op₁_first
        --   simp
        -- have h_a_concurrent_op₁_first : ∀ x, x ∈ ops₁_first → hb_concurrent hb x a := by
        --   intros; apply h_a_concurrent_op₁_first; simp; right; assumption
        -- rw [hb_concurrent_foldr h_concurrent h_a_concurrent_op₁_first]
        -- rw [<-effect_comp_assoc]
        -- have heq :
        --   ((effect b ▷ effect a) ▷ foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last))
        --     (map (fun a => effect a) ops₁_first)) s =
        --   ((effect b ▷ effect a) s) >>= foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last))
        --     (map (fun a => effect a) ops₁_first) := by
        --   simp [effect_comp]
        -- rw [heq, h_commutative b a]
        -- . have heq :
        --     (effect a ▷ effect b) s >>=
        --       foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last)) (map (fun a => effect a) ops₁_first) =
        --     ((effect a ▷ effect b) ▷ foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last))
        --       (map (fun a => effect a) ops₁_first)) s := by
        --     simp [effect_comp]
        --   rw [heq]
        --   rw [effect_comp_assoc]
        --   rw [effect_comp_apply]
        --   rw [effect_comp_apply]
        --   cases heq : effect a s with
        --   | error e => rfl
        --   | ok s' =>
        --     simp [bind, Except.bind.eq_2]
        --     rw [ih (b :: ops₁_first ++ ops₁_last)]
        --     . simp
        --     . cases h_consistent₀
        --       assumption
        --     . apply hb_consistent_sublist _ h_consistent₁
        --       simp
        --     . cases hcompatible₀; grind
        --     . cases hcompatible₁

        --     . intros x y h_x_mem h_ey_mem h_concurrent
        --       apply h_commutative
        --       simp; right; assumption
        --       simp; right; assumption
        --       assumption
        --     . simp at no_dup₀
        --       obtain ⟨ ⟩ := no_dup₀
        --       assumption
        --     . apply Nodup.sublist _ no_dup₁
        --       simp
        --     -- . intros op h_op_mem
        --     --   obtain ⟨ ops', hops' ⟩ := h_compatible op (by simp [h_op_mem])
        --     --   use ops' ++ [a]
        --     --   sorry
        --     . intros x
        --       constructor
        --       . intro h_mem₀
        --         have h_mem₀_cons : x ∈ a :: ops₀ := by
        --           simp; right; assumption
        --         rw [h_mem] at h_mem₀_cons
        --         simp at *
        --         rcases h_mem₀_cons with h_eq' | ⟨ h | ⟨ h | h ⟩ ⟩
        --         . left; assumption
        --         . right; left; assumption
        --         . subst h; obtain ⟨ h_eq'', _ ⟩ := no_dup₀
        --           contradiction
        --         . right; right; assumption
        --       . grind
        -- . rw [h_mem]
        --   simp
        -- . simp
        -- . simp [hb_concurrent] at *
        --   obtain ⟨ h_not_le_ab, h_not_le_ba ⟩ := h_a_b_concurrent
        --   constructor <;> assumption
        -- . cases hcompatible₁; grind
        -- . cases hcompatible₀; grind

end commutativity
