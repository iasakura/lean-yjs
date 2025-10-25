import Mathlib.Order.Defs.PartialOrder

import LeanYjs.Network.Basic

abbrev CausalOrder A := PartialOrder A

section CausalOrder

variable {A : Type} [DecidableEq A] (hb : CausalOrder A)

def hb_concurrent (a b : A) : Prop :=
  ¬ (hb.le a b) ∧ ¬ (hb.le b a)

def hb_consistent (list : List A) : Prop :=
  ∀ a b, a ∈ list → b ∈ list → list.idxOf? a < list.idxOf? b → hb.le a b

def concurrent_commutative (list : List A) (f : A → σ → (Except ε) σ) : Prop :=
  ∀ a b, a ∈ list → b ∈ list → hb_concurrent hb a b →
  ∀ s,
    (f a s >>= f b) = (f b s >>= f a)

theorem convergent (ops : List A) (init : σ) (f : A → σ → (Except ε) σ)
  (h_consistent : hb_consistent hb ops)
  (h_commutative : concurrent_commutative hb ops f) :
  ∀ permuted_ops,
    (∀ a, a ∈ ops ↔ a ∈ permuted_ops) →
    (List.foldlM f init ops) = (List.foldlM f init permuted_ops) :=

end CausalOrder
