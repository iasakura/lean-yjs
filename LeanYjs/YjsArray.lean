import LeanYjs.YjsArray.Invariant
import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.ItemOrder
import LeanYjs.ItemSetInvariant
import LeanYjs.Totality
import LeanYjs.Transitivity
import LeanYjs.Asymmetry
import LeanYjs.Integrate

section YjsArrInvariant

theorem idx_lt_getElem_YjsLt' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i < j) ->
  (hjsize : j < arr.size) ->
  YjsLt' (A := A) arr[i] arr[j] := by
  intros hinv hij hjsize
  apply List.Pairwise_idx_lt_p (P := fun x y => YjsLt' (YjsPtr.itemPtr x) y) <;> try assumption
  apply hinv.sorted

theorem idx_leq_getElem_YjsLeq' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i ≤ j) ->
  (hjsize : j < arr.size) ->
  YjsLeq' (A := A) arr[i] arr[j] := by
  intros hinv hij hjsize
  rw [Nat.le_iff_lt_or_eq] at hij
  cases hij with
  | inl hij =>
    have ⟨ _, hlt ⟩ : YjsLt' (A := A) arr[i] arr[j] := by
      apply idx_lt_getElem_YjsLt' arr i j hinv hij hjsize
    constructor
    right
    assumption
  | inr heq =>
    subst heq
    exists 0
    apply YjsLeq.leqSame

theorem YjsArrayInvariant_lt_neq (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hilt : i < arr.size) ->
  (hjlt : j < arr.size) ->
  i < j ->
  arr[i] ≠ arr[j] := by
  intros hinv hilt hjlt hij
  apply List.Pairwise_idx_lt_p (P := fun x y => x ≠ y) arr.toList i j hinv.unique hij hilt hjlt

theorem getElem_YjsLt'_idx_lt [DecidableEq A] (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hi_lt : i < arr.size) -> (hj_lt : j < arr.size) ->
  YjsLt' (A := A) arr[i] arr[j] ->
  i < j := by
  intros hinv hi_lt hj_lt hlt
  have hij_or : i < j ∨ i ≥ j := by
    apply Nat.lt_or_ge
  cases hij_or with
  | inl hij => assumption
  | inr hij =>
    have hleq : YjsLeq' (A := A) arr[j] arr[i] := by
      apply idx_leq_getElem_YjsLeq' arr j i hinv hij hi_lt
    by_contra
    apply yjs_lt_of_not_leq hinv.item_set_inv _ _ hinv.closed _ _ hlt hleq
    simp [ArrSet]
    simp [ArrSet]

end YjsArrInvariant

section FindPtrIdx

variable {A : Type}
variable [DecidableEq A]

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

theorem findPtrIdx_getElem (arr : Array (YjsItem A)) (i :  ℕ) :
  YjsArrInvariant arr.toList ->
  (hlt : i < arr.size) ->
  findPtrIdx arr[i] arr = Except.ok ↑i := by
  intros hinv hlt
  simp [findPtrIdx]
  suffices Array.findIdx? (fun x => x = arr[i]) arr = some i by
    rw [this]
    eq_refl
  rw [Array.findIdx?_eq_some_iff_getElem]
  constructor
  constructor
  . simp
  . intros j hij heq
    apply YjsArrayInvariant_lt_neq arr j i hinv (by omega) hlt hij (by simp at heq; assumption)
  . assumption

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

theorem findPtrIdx_lt_YjsLt' (arr : Array (YjsItem A)) (x y : YjsPtr A) :
  YjsArrInvariant arr.toList ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i < j ->
  YjsLt' x y := by
  intros hinv hfindx hfindy hlt
  have hinx : ArrSet arr.toList x := by
    cases x with
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]
    | itemPtr x =>
      apply findPtrIdx_item_exists arr x at hfindx
      obtain ⟨ j, heq, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      subst hfindx
      simp [ArrSet]
  have hiny : ArrSet arr.toList y := by
    cases y with
    | first =>
      simp [ArrSet]
    | last =>
      simp [ArrSet]
    | itemPtr y =>
      apply findPtrIdx_item_exists arr y at hfindy
      obtain ⟨ j, heq, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      subst hfindy
      simp [ArrSet]
  cases x with
  | first =>
    cases y with
    | first =>
      cases hfindx
      cases hfindy
      omega
    | last =>
      constructor
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_first_last
    | itemPtr y =>
      constructor
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_first
  | last =>
    cases y with
    | first =>
      cases hfindx
      cases hfindy
      omega
    | last =>
      cases hfindx
      cases hfindy
      omega
    | itemPtr y =>
      cases hfindx
      apply findPtrIdx_item_exists arr y at hfindy
      obtain ⟨ k, heq, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      unfold Int.toNat? at heq
      cases j <;> cases heq
      simp at hlt
      omega
  | itemPtr x =>
    cases y with
    | first =>
      cases hfindy
      apply findPtrIdx_item_exists arr x at hfindx
      obtain ⟨ k, heq, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      cases i <;> cases heq
      simp at hlt
      omega
    | last =>
      constructor
      apply YjsLt.ltOriginOrder
      apply OriginLt.lt_last
    | itemPtr y =>
      apply findPtrIdx_item_exists arr x at hfindx
      obtain ⟨ ix, heqx, hfindx ⟩ := hfindx
      rw [Array.getElem?_eq_some_iff] at hfindx
      obtain ⟨ _, hfindx ⟩ := hfindx
      subst hfindx

      apply findPtrIdx_item_exists arr y at hfindy
      obtain ⟨ iy, heqy, hfindy ⟩ := hfindy
      rw [Array.getElem?_eq_some_iff] at hfindy
      obtain ⟨ _, hfindy ⟩ := hfindy
      subst hfindy

      apply List.Pairwise_idx_lt_p (P := fun x y => YjsLt' (YjsPtr.itemPtr x) y)
      . apply hinv.sorted
      . cases i <;> cases heqx
        cases j <;> cases heqy
        rw [<-Int.ofNat_lt]
        assumption

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

theorem findPtrIdx_leq_YjsLeq' (arr : Array (YjsItem A)) (x y : YjsPtr A) :
  YjsArrInvariant arr.toList ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i ≤ j ->
  YjsLeq' x y := by
  intros hinv hfindx hfindy hleq
  have hor : i < j ∨ i = j := by omega
  cases hor with
  | inl hor =>
    apply YjsLeq'.leqLt
    apply findPtrIdx_lt_YjsLt' _ _ _ hinv hfindx hfindy hor
  | inr heq =>
    subst heq
    have heq : x = y := by
      apply findPtrIdx_eq_ok_inj x y hfindx hfindy
    subst x
    apply YjsLeq'.leqSame

lemma YjsLt'_findPtrIdx_idx_lt (i j : ℤ) (x y : YjsPtr A) (arr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList ->
  ArrSet arr.toList x -> ArrSet arr.toList y ->
  YjsLt' (A := A) x y ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i < j := by
  intros hinv harrx harry hlt hleft hright
  cases x with
  | last =>
    obtain ⟨ _, hlt ⟩ := hlt
    by_contra
    apply not_last_lt_ptr hinv.closed hinv.item_set_inv at hlt <;> assumption
  | first =>
    cases y with
    | first =>
      obtain ⟨ _, hlt ⟩ := hlt
      by_contra
      apply not_ptr_lt_first hinv.closed hinv.item_set_inv at hlt <;> assumption
    | itemPtr r =>
      simp only [findPtrIdx] at hleft hright
      generalize heqright : Array.findIdx? (fun i => decide (i = r)) arr = right at hright
      cases right with
      | none => simp at hright
      | some left =>
        cases hleft
        cases hright
        omega
    | last =>
      simp only [findPtrIdx] at hleft hright
      cases hleft
      cases hright
      omega
  | itemPtr o =>
    cases y with
    | first =>
      obtain ⟨ _, hlt ⟩ := hlt
      by_contra
      apply not_ptr_lt_first hinv.closed hinv.item_set_inv at hlt <;> assumption
    | last =>
      simp only [findPtrIdx] at hleft hright
      generalize heqleft : Array.findIdx? (fun i => decide (i = o)) arr = left at hleft
      cases left with
      | none => simp at hleft
      | some left =>
        cases hleft
        cases hright
        rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heqleft
        omega
    | itemPtr r =>
      simp only [findPtrIdx] at hleft hright
      generalize heqleft : Array.findIdx? (fun i => decide (i = o)) arr = left at hleft
      generalize heqright : Array.findIdx? (fun i => decide (i = r)) arr = right at hright
      cases left with
      | none => simp at hleft
      | some left =>
        cases right with
        | none => simp at hright
        | some right =>
          rw [Array.findIdx?_eq_some_iff_getElem] at heqleft heqright
          obtain ⟨ _, hgetElemLeft, _ ⟩ := heqleft
          obtain ⟨ _, hgetElemRight, _ ⟩ := heqright
          simp at *
          cases hleft
          cases hright
          simp
          subst hgetElemLeft
          subst hgetElemRight
          apply getElem_YjsLt'_idx_lt _ _ _ hinv _ _ hlt

theorem YjsLeq'_findPtrIdx_leq (i j : ℤ) (x y : YjsPtr A) (arr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList ->
  ArrSet arr.toList x -> ArrSet arr.toList y ->
  YjsLeq' x y ->
  findPtrIdx x arr = Except.ok i ->
  findPtrIdx y arr = Except.ok j ->
  i ≤ j := by
  intros hinv harrx harry hleq hleft hright
  apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
  cases hleq with
  | inl heq =>
    subst heq
    rw [hleft] at hright
    cases hright
    simp
  | inr hlt =>
    suffices h : i < j by omega
    apply YjsLt'_findPtrIdx_idx_lt _ _ _ _ _ hinv harrx harry hlt hleft hright

theorem findPtrIdx_origin_leq_newItem_YjsLt' {arr : Array (YjsItem A)} {other newItem : YjsItem A} :
  (∀i, i ∈ arr → i ∈ ls) ->
  (newItem ∈ ls) ->
  (other ∈ ls) ->
  (hclosed : IsClosedItemSet $ ArrSet ls) ->
  (harrsetinv : ItemSetInvariant $ ArrSet ls) ->
  (harrinv : YjsArrInvariant arr.toList) ->
  YjsArrInvariant arr.toList ->
  findPtrIdx newItem.origin arr = Except.ok leftIdx ->
  findPtrIdx newItem.rightOrigin arr = Except.ok rightIdx ->
  findPtrIdx other.origin arr = Except.ok oLeftIdx ->
  findPtrIdx other.rightOrigin arr = Except.ok oReftIdx ->
  YjsLt' newItem.origin other ->
  YjsLt' other newItem.rightOrigin ->
  leftIdx ≤ oLeftIdx ->
  (leftIdx = oLeftIdx -> other.id < newItem.id) ->
  YjsLt' other.origin newItem ->
  YjsLt' (A := A) other newItem := by
  intros hsubset hnewItem_in_ls hother_in_ls hclosed harrsetinv harrinv hinv hfindLeft hfindRight hfindOLeft hfindORight h_newItem_origin_lt_other h_origin_lt_newItem_rightOrigin heq_oleft heq_oleft_eq hlt_oleft_newItem
  have hor : YjsLeq' other.rightOrigin newItem ∨ YjsLt' newItem other.rightOrigin := by
    apply yjs_lt_total (P := ArrSet $ ls) <;> try assumption
    . obtain ⟨ o, r, id, c ⟩ := other
      apply hclosed.closedRight o r id c
      simp [ArrSet]
      assumption
  cases hor with
  | inl hle =>
    obtain ⟨ _, hle ⟩ := hle
    obtain ⟨ o, r, id, c ⟩ := other
    constructor
    apply YjsLt.ltRightOrigin
    assumption
  | inr hlt =>
    have hor : leftIdx < oLeftIdx ∨ leftIdx = oLeftIdx := by
      omega
    cases hor with
    | inl hlt_left =>
      have heq_origin : YjsLt' newItem.origin other.origin := by
        apply findPtrIdx_lt_YjsLt' <;> assumption
      obtain ⟨ o, r, id, c ⟩ := other
      obtain ⟨ no, nr, nid, nc ⟩ := newItem
      simp [YjsItem.origin, YjsItem.rightOrigin] at heq_origin hlt
      apply YjsLt'.ltConflict
      apply ConflictLt'.ltOriginDiff <;> try assumption
    | inr heq_origin =>
      subst oLeftIdx
      have heq_origin : newItem.origin = other.origin := by
        apply findPtrIdx_eq_ok_inj _ _ hfindLeft hfindOLeft
      obtain ⟨ o, r, id, c ⟩ := other
      obtain ⟨ no, nr, nid, nc ⟩ := newItem
      simp [YjsItem.origin, YjsItem.rightOrigin, YjsItem.id] at heq_origin heq_oleft_eq hlt
      subst no
      apply YjsLt'.ltConflict
      apply ConflictLt'.ltOriginSame <;> try assumption

lemma findPtrIdx_lt_size_getElem {p : YjsPtr A} :
  findPtrIdx p arr = Except.ok idx →
  0 ≤ idx ->
  (h : idx.toNat < arr.size) →
  arr[idx.toNat] = p := by
  intros hfind hlt hsize
  unfold findPtrIdx at hfind
  cases p with
  | first =>
    simp at hfind
    cases hfind
    omega
  | last =>
    simp at hfind
    cases hfind
    omega
  | itemPtr p =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = p)) arr = idxOpt at hfind
    cases idxOpt <;> cases hfind
    rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, heq, _ ⟩ := heq
    simp at heq
    subst p
    simp

end FindPtrIdx
