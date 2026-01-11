theorem List.findIdx?_pred_eq_eq {A : Type} {arr : List A} {f g} :
  (∀a ∈ arr, f a = g a) →
  arr.findIdx? f = arr.findIdx? g := by
  intros h_mem
  induction arr with
  | nil =>
    simp
  | cons x xs ih =>
    grind

theorem Array.findIdx?_pred_eq_eq {A : Type} {arr : Array A} {f g} :
  (∀a ∈ arr, f a = g a) →
  Array.findIdx? f arr = Array.findIdx? g arr := by
  intros h_mem
  rw [List.findIdx?_toArray]
  rw [List.findIdx?_toArray]
  apply List.findIdx?_pred_eq_eq
  grind

theorem Array.findIdx?_insertIdxIfInBounds_none {A : Type} {arr : Array A} {idx : Nat} {a : A} {p} :
  p a = false →
  Array.findIdx? p arr = none →
  Array.findIdx? p (arr.insertIdxIfInBounds idx a) = none := by
  intros; simp at *
  intros x hx
  simp [Array.insertIdxIfInBounds] at hx
  grind [Array.mem_insertIdx]

theorem List.findIdx?_insertIdxIfInBounds_some {A : Type} {arr : List A} {idx : Nat} {a : A} {p} :
  p a = false →
  List.findIdx? p arr = some n →
  List.findIdx? p (arr.insertIdx idx a) = if n < idx then some n else some (n + 1) := by
  intros hpa hfind
  induction arr generalizing idx n with
  | nil =>
    simp at *
  | cons head tail ih =>
    cases idx with
    | zero =>
      grind
    | succ idx' =>
      simp at *
      rw [findIdx?_cons] at *
      cases hphead : p head with
      | true =>
        simp [hphead] at *
        grind
      | false =>
        simp [hphead] at *
        grind

theorem Array.findIdx?_insertIdxIfInBounds_some {A : Type} {arr : Array A} {idx : Nat} {a : A} {p} :
  p a = false →
  Array.findIdx? p arr = some n →
  Array.findIdx? p (arr.insertIdxIfInBounds idx a) = if n < idx then some n else some (n + 1) := by
  intros hpa hfind
  rw [List.findIdx?_toArray] at *
  simp [Array.insertIdxIfInBounds] at *
  split
  . simp
    grind [List.findIdx?_insertIdxIfInBounds_some]
  . rw [hfind]
    split
    . rfl
    . grind [List.findIdx?_eq_some_iff_findIdx_eq]

theorem Array.find?_insertIdxIfInBounds_none {A : Type} {arr : Array A} {idx : Nat} {a : A} {p} :
  p a = false →
  Array.find? p arr = none →
  Array.find? p (arr.insertIdxIfInBounds idx a) = none := by
  intros; simp at *
  intros x hx
  simp [Array.insertIdxIfInBounds] at hx
  grind [Array.mem_insertIdx]
