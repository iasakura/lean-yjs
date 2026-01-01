import LeanYjs.Algorithm.Insert.Basic

variable {A : Type} [DecidableEq A]

theorem findPtrIdx_item_exists (arr : Array (YjsItem A)) (x : YjsItem A) :
  findPtrIdx x arr = Except.ok i ->
  ∃j, i.toNat? = some j ∧ arr[j]? = some x := by
  intros hfind
  simp [findPtrIdx] at hfind
  generalize heq : Array.findIdx? (fun i => i = x) arr = idx at hfind
  cases idx <;> cases hfind
  constructor; constructor
  . unfold Int.toNat?
    eq_refl
  . rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, h1, h2 ⟩ := heq
    rw [Array.getElem?_eq_getElem]
    rw [decide_eq_true_eq] at h1
    simp; assumption

theorem findPtrIdx_eq_ok_inj {arr : Array (YjsItem A)} (x y : YjsPtr A) :
  findPtrIdx x arr = Except.ok i →
  findPtrIdx y arr = Except.ok i →
   x = y := by
  intros heq_x heq_y
  cases x with
  | first =>
    cases y with
    | first =>
      simp
    | last =>
      simp [findPtrIdx] at heq_x heq_y
      cases heq_x
      cases heq_y
    | itemPtr y =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = y)) arr = idx at *
      cases idx <;> cases heq_y
      cases heq_x
  | last =>
    cases y with
    | first =>
      simp [findPtrIdx] at heq_x heq_y
      cases heq_x
      cases heq_y
    | last =>
      simp
    | itemPtr y =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = y)) arr = idx at *
      cases idx <;> cases heq_y
      cases heq_x
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      omega
  | itemPtr x =>
    cases y with
    | first =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = x)) arr = idx at *
      cases idx <;> cases heq_x
      cases heq_y
    | last =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = x)) arr = idx at *
      cases idx <;> cases heq_x
      cases heq_y
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      omega
    | itemPtr y =>
      simp [findPtrIdx] at heq_x heq_y
      generalize heq_x :  Array.findIdx? (fun i => decide (i = x)) arr = idxX at *
      generalize heq_y :  Array.findIdx? (fun i => decide (i = y)) arr = idxY at *
      cases idxX <;> cases heq_x
      cases idxY <;> cases heq_y
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq_x
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq_y
      obtain ⟨ hlt_x, heq_x ⟩ := heq_x
      obtain ⟨ hlt_y, heq_y ⟩ := heq_y
      rw [Array.findIdx_eq hlt_x] at heq_x
      rw [Array.findIdx_eq hlt_y] at heq_y
      simp at heq_x heq_y
      obtain ⟨ heq_x, _ ⟩ := heq_x
      obtain ⟨ heq_y, _ ⟩ := heq_y
      subst x y
      simp

theorem findPtrIdx_ge_minus_1 {arr : Array (YjsItem A)} (item : YjsPtr A) :
  findPtrIdx item arr = Except.ok idx
  -> idx ≥ -1 := by
  intros hfind
  unfold findPtrIdx at hfind
  cases item with
  | first =>
    simp at hfind
    cases hfind
    simp
  | last =>
    simp at hfind
    cases hfind
    omega
  | itemPtr item =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = item)) arr = idx at hfind
    cases idx with
    | none =>
      cases hfind
    | some idx =>
      cases hfind
      omega

theorem findPtrIdx_le_size {arr : Array (YjsItem A)} (item : YjsPtr A) :
  findPtrIdx item arr = Except.ok idx
  -> idx ≤ arr.size := by
  intros hfind
  unfold findPtrIdx at hfind
  cases item with
  | first =>
    simp at hfind
    cases hfind
    omega
  | last =>
    simp at hfind
    cases hfind
    simp
  | itemPtr item =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = item)) arr = idx at hfind
    cases idx with
    | none =>
      cases hfind
    | some idx =>
      cases hfind
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      obtain ⟨ _, _ ⟩ := heq
      simp
      omega
