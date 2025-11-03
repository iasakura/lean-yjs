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


theorem List.filterMap_getElem? : forall {A B} (f : A → Option B) (l : List A) (i : Nat),
  (i < (l.filterMap f).length) →
  ∃ a, a ∈ l ∧ f a = (l.filterMap f)[i]? := by
  intros A B f l i hlt
  generalize h_l_filterMap : l.filterMap f = l' at *
  induction l generalizing l' i with
  | nil =>
    simp [List.filterMap] at h_l_filterMap
    subst l'; simp at hlt
  | cons a l ih =>
    simp [List.filterMap_cons] at h_l_filterMap
    generalize h_f_a : f a = fa at h_l_filterMap
    cases fa with
    | none =>
      simp at h_l_filterMap
      have ⟨a, h_a_mem, h_a ⟩ : ∃a ∈ l, f a = l'[i]? := by
        apply ih _ _ h_l_filterMap
        assumption
      exists a
      constructor
      . simp; right; assumption
      . assumption
    | some b =>
      simp at h_l_filterMap
      cases h_l_filterMap
      simp at hlt
      cases i with
      | zero =>
        exists a
        rw [h_f_a]
        simp
      | succ i =>
        simp at hlt
        have ⟨ a, h_mem, h_ih ⟩ : ∃ a ∈ l, f a = (List.filterMap f l)[i]? := by
          apply ih i (List.filterMap f l) _ hlt; simp
        exists a; simp
        constructor;
        . right; assumption
        . assumption

theorem List.filterMap_getElem_index : forall {A B} (f : A → Option B) (l : List A),
  ∃map : Nat → Nat,
    (∀i, i < (List.filterMap f l).length → ∃ x, (List.filterMap f l)[i]? = f x ∧ l[map i]? = some x) ∧
    (∀i j, i < (List.filterMap f l).length → j < (List.filterMap f l).length →
      map i = map j → i = j) := by
  intros A B f l
  induction l with
  | nil =>
    exists fun _ => 0
    constructor
    . intros i hlt
      simp at hlt
    . intros i j hlt_i hlt_j h_eq
      simp at hlt_i
  | cons a l ih =>
    obtain ⟨ map, h_map_eq, h_map_inj ⟩ := ih
    simp [List.filterMap_cons]
    generalize h_f_a : f a = fa at *
    cases fa with
    | none =>
      exists (fun x => map x + 1)
      simp
      constructor
      . intros i hlt
        specialize h_map_eq i hlt
        obtain ⟨ x, h_f_x, h_l_map_i ⟩ := h_map_eq
        exists x
      . apply h_map_inj
    | some b =>
      simp
      exists fun x =>
        if x = 0 then 0 else map (x - 1) + 1
      constructor
      . intros i hlt
        cases i with
        | zero =>
          exists a
          rw [h_f_a]
          simp
        | succ i =>
          specialize h_map_eq i (by omega)
          obtain ⟨ x, h_f_x, h_l_map_i ⟩ := h_map_eq
          exists x
      . intros i j hlt_i hlt_j h_eq
        cases i with
        | zero =>
          cases j with
          | zero =>
            rfl
          | succ j =>
            simp at h_eq
        | succ i =>
          cases j with
          | zero =>
            simp at h_eq
          | succ j =>
            simp at h_eq
            have h_eq : i = j := by
              apply h_map_inj _ _ _ _ h_eq
              . omega
              . omega
            . omega

theorem List.getElem_eq_iff_getElem?_eq (l : List A) (i j : Nat) (hlt_i : i < l.length) (hlt_j : j < l.length) :
  l[i] = l[j] ↔ l[i]? = l[j]? := by
  constructor
  . intros h_eq
    rw [List.getElem_eq_iff] at h_eq
    rw [h_eq]
    simp
  . intros h_eq
    rw [List.getElem?_eq_getElem hlt_i] at h_eq
    rw [List.getElem?_eq_getElem hlt_j] at h_eq
    simp at h_eq
    assumption

theorem List.no_dup_cons_eq (a : A) {ops₀ ops₁ : List A} :
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
