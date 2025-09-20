import Mathlib.Data.Nat.Basic

theorem List.Pairwise_insertIdx {R : A -> A -> Prop} (l : List A) (i : ℕ) (newItem : A) :
  (hilength : i ≤ l.length)
  -> List.Pairwise R l
  -> (∀j, (hji : j < i) -> R (l[j]) newItem)
  -> (∀j, (hji : i <= j) -> (hjlen : j < l.length) -> R newItem (l[j]))
  -> List.Pairwise R (l.insertIdx i newItem) := by
  intros hilength hpair hlt1 hlt2
  rw [List.pairwise_iff_getElem] at *
  intros j k hjlen hklen hjk
  rw [List.length_insertIdx_of_le_length] at * <;> try assumption
  have hjk :
    (j = i ∧ i < k) ∨
    (j < i ∧ k = i) ∨
    (j ≠ i ∧ i ≠ k) := by
    omega
  cases hjk with
  | inl hjk =>
    obtain ⟨ heq, hik ⟩ := hjk
    subst heq
    rw [List.getElem_insertIdx (i := j) (j := j)]
    simp
    rw [List.getElem_insertIdx (i := j) (j := k)]
    split; omega
    split; omega
    apply hlt2; omega
  | inr hjk =>
    cases hjk with
    | inl hjk =>
      obtain ⟨ hjk, heq ⟩ := hjk
      subst heq
      simp
      rw [List.getElem_insertIdx (i := k) (j := j)]
      split; apply hlt1; omega
      omega
    | inr hjk =>
      obtain ⟨ hji, hki ⟩ := hjk
      rw [List.getElem_insertIdx (i := i) (j := j)]
      rw [List.getElem_insertIdx (i := i) (j := k)]
      split
      split
      apply hpair; omega
      split; omega
      apply hpair; omega
      split; apply hpair; omega
      split; omega
      apply hpair; omega

theorem List.Pairwise_weaken {A : Type} {R Q : A -> A -> Prop} [DecidableEq A] (l : List A) :
  List.Pairwise R l
  -> (∀ a b, R a b -> Q a b)
  -> List.Pairwise Q l := by
  intros hpair hweak
  rw [List.pairwise_iff_getElem] at *
  intros
  apply hweak
  apply hpair
  assumption
