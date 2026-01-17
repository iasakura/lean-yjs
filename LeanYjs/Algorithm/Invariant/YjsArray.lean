import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality
import LeanYjs.Order.Transitivity
import LeanYjs.Order.Asymmetry
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Insert.Lemmas
import LeanYjs.Algorithm.Invariant.Lemmas
import LeanYjs.Algorithm.Invariant.Basic

variable {A : Type}
variable [DecidableEq A]

abbrev uniqueId (items : List (YjsItem A)) : Prop :=
  List.Pairwise (fun x y => x.id ≠ y.id) items

structure YjsArrInvariant (arr : List (YjsItem A)) : Prop where
  closed : IsClosedItemSet (ArrSet arr)
  item_set_inv : ItemSetInvariant (ArrSet arr)
  sorted : List.Pairwise (fun (x y : YjsItem A) => YjsLt' (A := A) x y) arr
  unique : uniqueId arr

theorem same_yjs_set_unique_aux (xs_all ys_all xs ys : List (YjsItem A)) :
  YjsArrInvariant xs_all ->
  YjsArrInvariant ys_all ->
  (∀ a, ArrSet xs_all a ↔ ArrSet ys_all a) ->
  (∃ t, t ++ xs = xs_all) ->
  (∃ t, t ++ ys = ys_all) ->
  (∀ x, ArrSet xs x ↔ ArrSet ys x) ->
  xs = ys := by
  intros hinv1 hinv2 hseteq_all hsubset1 hsubset2 hseteq
  obtain ⟨ hclosed1, hinv1, hsort1, huniq1 ⟩ := hinv1
  obtain ⟨ hclosed2, hinv2, hsort2, huniq2 ⟩ := hinv2

  revert ys

  induction xs with
  | nil =>
    intros ys hsubset2 hseteq
    cases ys with
    | nil => eq_refl
    | cons y ys =>
      obtain hitem := hseteq y
      simp [ArrSet] at hitem
  | cons x xs ih =>
    intros ys hsubset2 hseteq
    cases ys with
    | nil =>
      obtain hitem := hseteq x
      simp [ArrSet] at hitem
    | cons y ys =>
      have hmin1 : ∀ a ∈ xs, YjsLt' (A := A) x a := by
        obtain ⟨ t, heq ⟩ := hsubset1
        subst heq
        rw [List.pairwise_append] at hsort1
        obtain ⟨ _, hsort1, _ ⟩ := hsort1
        simp at hsort1
        obtain ⟨ hsort1, _ ⟩ := hsort1
        assumption
      have hmin2 : ∀ a ∈ ys, YjsLt' (A := A) y a := by
        obtain ⟨ t, heq ⟩ := hsubset2
        subst heq
        rw [List.pairwise_append] at hsort2
        obtain ⟨ _, hsort2, _ ⟩ := hsort2
        simp at hsort2
        obtain ⟨ hsort2, _ ⟩ := hsort2
        assumption

      have heq : x = y := by
        have hlt1 : x = y ∨ YjsLt' (A := A) y x := by
          cases (inferInstance : Decidable (x = y)) with
          | isTrue heq =>
            left; assumption
          | isFalse hneq =>
            obtain ⟨ hinx, _ ⟩ := hseteq x
            have hinx : x = y ∨ x ∈ ys:= by
              simp [ArrSet] at hinx
              assumption
            cases hinx with
            | inl heq =>
              left; assumption
            | inr hinx =>
              apply hmin2 at hinx
              obtain ⟨ _, hinx ⟩ := hinx
              right
              constructor
              assumption

        have hlt2 : x = y ∨ YjsLt' (A := A) x y := by
          cases (inferInstance : Decidable (x = y)) with
          | isTrue heq =>
            subst heq; left; eq_refl
          | isFalse hneq =>
            obtain ⟨ _, hinx ⟩ := hseteq y
            have hiny : y = x ∨ y ∈ xs:= by
              simp [ArrSet] at hinx
              assumption
            cases hiny with
            | inl heq =>
              subst heq; left; eq_refl
            | inr hiny =>
              apply hmin1 at hiny
              obtain ⟨ _, hiny ⟩ := hiny
              right
              constructor
              assumption

        cases hlt1 with
        | inl heq =>
          assumption
        | inr hlt1 =>
          cases hlt2 with
          | inl heq =>
            assumption
          | inr hlt2 =>
            obtain ⟨ tx, heq1 ⟩ := hsubset1
            obtain ⟨ ty, heq2 ⟩ := hsubset2
            subst heq1 heq2
            cases yjs_lt_asymm hclosed2 hinv2 x y (by rw [<-hseteq_all]; simp [ArrSet]) (by simp [ArrSet]) hlt2 hlt1

      subst heq
      congr

      apply ih
      . obtain ⟨ t, heq ⟩ := hsubset1
        subst heq
        exists (t ++ [x])
        simp
      . obtain ⟨ t, heq ⟩ := hsubset2
        subst heq
        exists (t ++ [x])
        simp
      . intros a
        simp [ArrSet] at *
        cases a with
        | first =>
          simp
        | last =>
          simp
        | itemPtr a =>
          specialize hseteq a
          simp at *
          obtain ⟨ t, heq ⟩ := hsubset1
          subst heq
          obtain ⟨ t', heq ⟩ := hsubset2
          subst heq
          simp [uniqueId] at *
          rw [List.pairwise_append] at huniq1
          rw [List.pairwise_append] at huniq2
          simp at *
          obtain ⟨ _, ⟨ huniq1, _ ⟩, _ ⟩ := huniq1
          obtain ⟨ _, ⟨ huniq2, _ ⟩ , _ ⟩ := huniq2
          constructor
          . intros hin
            obtain hneq := huniq1 _ hin
            have h : a = x ∨ a ∈ ys := by
              rw [<-hseteq]
              right; assumption
            cases h with
            | inl heq =>
              subst heq
              cases hneq (refl _)
            | inr hin =>
              assumption
          . intros hin
            obtain hneq := huniq2 _ hin
            have h : a = x ∨ a ∈ xs := by
              rw [hseteq]
              right; assumption
            cases h with
            | inl heq =>
              subst heq
              cases hneq (refl _)
            | inr hin =>
              assumption

theorem same_yjs_set_unique (xs ys : List (YjsItem A)) :
  YjsArrInvariant xs ->
  YjsArrInvariant ys ->
  (∀ a, ArrSet xs a ↔ ArrSet ys a) ->
  xs = ys := by
  intros hinv1 hinv2 hseteq
  apply same_yjs_set_unique_aux xs ys xs ys hinv1 hinv2 hseteq
  . exists []
  . exists []
  . apply hseteq

private theorem idx_lt_pairwise {α} {P : α -> α -> Prop} (xs : List α) (i j : Nat) :
  List.Pairwise (fun (x y : α) => P x y) xs ->
  i < j ->
  (hlt_x : i < xs.length) ->
  (hlt_y : j < xs.length) ->
  P (xs[i]) (xs[j]) := by
  revert i j
  induction xs with
  | nil =>
    intros i j hpair hlt_ij hlt_x hlt_y
    simp [List.length] at hlt_x
  | cons x xs ih =>
    intros i j hpair hlt_ij hlt_x hlt_y
    simp at *
    cases i <;> cases j <;> try omega
    . simp
      obtain ⟨ h, _ ⟩ := hpair
      apply h; simp
    . simp
      apply ih
      . obtain ⟨ _, hpair ⟩ := hpair
        apply hpair
      . omega

omit [DecidableEq A] in private theorem getElem_lt_YjsLt' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i < j) ->
  (hjsize : j < arr.size) ->
  YjsLt' (A := A) arr[i] arr[j] := by
  intros hinv hij hjsize
  apply idx_lt_pairwise (P := fun x y => YjsLt' (YjsPtr.itemPtr x) y) <;> try assumption
  apply hinv.sorted

omit [DecidableEq A] in theorem getElem_leq_YjsLeq' (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hij : i ≤ j) ->
  (hjsize : j < arr.size) ->
  YjsLeq' (A := A) arr[i] arr[j] := by
  intros hinv hij hjsize
  rw [Nat.le_iff_lt_or_eq] at hij
  cases hij with
  | inl hij =>
    have ⟨ _, hlt ⟩ : YjsLt' (A := A) arr[i] arr[j] := by
      apply getElem_lt_YjsLt' arr i j hinv hij hjsize
    constructor
    right
    assumption
  | inr heq =>
    subst heq
    exists 0
    apply YjsLeq.leqSame

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

      apply idx_lt_pairwise (P := fun x y => YjsLt' (YjsPtr.itemPtr x) y)
      . apply hinv.sorted
      . cases i <;> cases heqx
        cases j <;> cases heqy
        rw [<-Int.ofNat_lt]
        assumption

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

theorem getElem_YjsLt'_index_lt (arr : Array (YjsItem A)) (i j : Nat) :
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
      apply getElem_leq_YjsLeq' arr j i hinv hij hi_lt
    by_contra
    apply yjs_lt_of_not_leq hinv.item_set_inv _ _ hinv.closed _ _ hlt hleq
    simp [ArrSet]
    simp [ArrSet]

lemma YjsLt'_findPtrIdx_lt (i j : ℤ) (x y : YjsPtr A) (arr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList →
  ArrSet arr.toList x → ArrSet arr.toList y →
  YjsLt' (A := A) x y →
  findPtrIdx x arr = Except.ok i →
  findPtrIdx y arr = Except.ok j →
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
          apply getElem_YjsLt'_index_lt _ _ _ hinv _ _ hlt

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
    apply YjsLt'_findPtrIdx_lt _ _ _ _ _ hinv harrx harry hlt hleft hright

omit [DecidableEq A] in private theorem YjsArrayInvariant_lt_neq (arr : Array (YjsItem A)) (i j : Nat) :
  YjsArrInvariant arr.toList ->
  (hilt : i < arr.size) ->
  (hjlt : j < arr.size) ->
  i < j ->
  arr[i] ≠ arr[j] := by
  intros hinv hilt hjlt hij
  have h := idx_lt_pairwise (P := fun x y => x.id ≠ y.id) arr.toList i j hinv.unique hij hilt hjlt
  simp at h
  grind only

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
    . obtain ⟨ o, r, id, c, d ⟩ := other
      apply hclosed.closedRight o r id c
      simp [ArrSet]
      assumption
  cases hor with
  | inl hle =>
    obtain ⟨ _, hle ⟩ := hle
    obtain ⟨ o, r, id, c, d ⟩ := other
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
      obtain ⟨ o, r, id, c, d ⟩ := other
      obtain ⟨ no, nr, nid, nc, nd ⟩ := newItem
      simp at heq_origin hlt
      apply YjsLt'.ltConflict
      apply ConflictLt'.ltOriginDiff <;> try assumption
    | inr heq_origin =>
      subst oLeftIdx
      have heq_origin : newItem.origin = other.origin := by
        apply findPtrIdx_eq_ok_inj _ _ hfindLeft hfindOLeft
      obtain ⟨ o, r, id, c, d ⟩ := other
      obtain ⟨ no, nr, nid, nc, nd ⟩ := newItem
      simp at heq_origin heq_oleft_eq hlt
      subst no
      apply YjsLt'.ltConflict
      apply ConflictLt'.ltOriginSame <;> try assumption

theorem findPtrIdx_ArrSet {A : Type} [DecidableEq A] {arr : Array (YjsItem A)} {p : YjsPtr A} {idx : ℤ} :
  findPtrIdx p arr = Except.ok idx →
  ArrSet arr.toList p := by
  intros hfind
  unfold findPtrIdx at hfind
  cases p with
  | first =>
    simp at hfind
    cases hfind
    simp [ArrSet]
  | last =>
    simp at hfind
    cases hfind
    simp [ArrSet]
  | itemPtr p =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = p)) arr = idxOpt at hfind
    cases idxOpt <;> cases hfind
    rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, heq, _ ⟩ := heq
    simp at heq
    subst p
    simp [ArrSet]

@[simp] abbrev isLeftIdPtr (arr : Array (YjsItem A)) (id : Option YjsId) (ptr : YjsPtr A) : Prop :=
  match id with
  | none => ptr = YjsPtr.first
  | some pid =>
    ∃(item : YjsItem A), ptr = YjsPtr.itemPtr item ∧ arr.find? (fun i => i.id = pid) = some item

theorem isLeftIdPtr_unique {A : Type} (arr : Array (YjsItem A)) (id : Option YjsId) (ptr1 ptr2 : YjsPtr A) :
  uniqueId arr.toList →
  isLeftIdPtr arr id ptr1 →
  isLeftIdPtr arr id ptr2 →
  ptr1 = ptr2 := by
  intros h_unique h_ptr1 h_ptr2
  cases id with
  | none =>
    simp [isLeftIdPtr] at h_ptr1 h_ptr2
    rw [h_ptr1, h_ptr2]
  | some pid =>
    simp [isLeftIdPtr] at h_ptr1 h_ptr2
    obtain ⟨ item1, heq1, hfind1 ⟩ := h_ptr1
    obtain ⟨ item2, heq2, hfind2 ⟩ := h_ptr2
    grind

@[simp] abbrev isRightIdPtr (arr : Array (YjsItem A)) (id : Option YjsId) (ptr : YjsPtr A) : Prop :=
  match id with
  | none => ptr = YjsPtr.last
  | some pid =>
    ∃(item : YjsItem A), ptr = YjsPtr.itemPtr item ∧ arr.find? (fun i => i.id = pid) = some item

theorem isRightIdPtr_unique {A : Type} (arr : Array (YjsItem A)) (id : Option YjsId) (ptr1 ptr2 : YjsPtr A) :
  uniqueId arr.toList →
  isRightIdPtr arr id ptr1 →
  isRightIdPtr arr id ptr2 →
  ptr1 = ptr2 := by
  intros h_unique h_ptr1 h_ptr2
  cases id with
  | none =>
    simp [isRightIdPtr] at h_ptr1 h_ptr2
    rw [h_ptr1, h_ptr2]
  | some pid =>
    simp [isRightIdPtr] at h_ptr1 h_ptr2
    obtain ⟨ item1, heq1, hfind1 ⟩ := h_ptr1
    obtain ⟨ item2, heq2, hfind2 ⟩ := h_ptr2
    grind

-- TODO: refactor proof
-- YjsArrInvariant is needed to ensure the array is unique and
theorem IntegrateInput.toItem_ok_iff {A : Type} (input : IntegrateInput A) (arr : Array (YjsItem A)) (newItem : YjsItem A) :
  uniqueId arr.toList →
  (input.toItem arr = Except.ok newItem ↔
  ∃origin rightOrigin id content,
    newItem = YjsItem.mk origin rightOrigin id content false ∧
    isLeftIdPtr arr input.originId origin ∧
    isRightIdPtr arr input.rightOriginId rightOrigin ∧
    id = input.id ∧
    content = input.content) := by
  intros h_unique
  constructor
  . intros h_toItem
    simp [IntegrateInput.toItem] at h_toItem
    cases h_originId : input.originId with
    | none =>
      simp [h_originId] at h_toItem
      cases h_rightOriginId : input.rightOriginId with
      | none =>
        simp [h_rightOriginId] at h_toItem
        cases h_toItem
        simp
      | some rightOrigin =>
        simp [h_rightOriginId] at h_toItem
        cases h_find : Array.find? (fun item => decide (item.id = rightOrigin)) arr with
        | none =>
          simp [h_find] at h_toItem
          cases h_toItem
        | some rightOriginItem =>
          simp [h_find] at h_toItem
          cases h_toItem
          grind only [→ Array.mem_of_find?_eq_some, → Array.find?_some]
    | some origin =>
      simp [h_originId] at h_toItem
      cases h_find_origin : Array.find? (fun item => decide (item.id = origin)) arr with
      | none =>
        simp [h_find_origin] at h_toItem
        cases h_toItem
      | some originItem =>
        simp [h_find_origin] at h_toItem
        cases h_rightOriginId : input.rightOriginId with
        | none =>
          simp [h_rightOriginId] at h_toItem
          cases h_toItem
          grind only [→ Array.mem_of_find?_eq_some, → Array.find?_some]
        | some rightOrigin =>
          simp [h_rightOriginId] at h_toItem
          cases h_find : Array.find? (fun item => decide (item.id = rightOrigin)) arr with
          | none =>
            simp [h_find] at h_toItem
            cases h_toItem
          | some rightOriginItem =>
            simp [h_find] at h_toItem
            cases h_toItem
            grind only [→ Array.mem_of_find?_eq_some, → Array.find?_some]
  . intros h_exists
    obtain ⟨ origin, rightOrigin, id, content, hdef, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_exists
    simp [IntegrateInput.toItem]
    cases h_originId : input.originId with
    | none =>
      rw [h_originId] at h_origin
      simp [h_originId] at *
      cases h_rightOriginId : input.rightOriginId with
      | none =>
        rw [h_rightOriginId] at h_rightOrigin
        simp [h_rightOriginId] at *
        rw [hdef, h_origin, h_rightOrigin, h_id, h_content]
        rfl
      | some rightOriginId =>
        simp
        rw [h_rightOriginId] at h_rightOrigin
        simp at h_rightOrigin
        obtain ⟨ rightOriginItem, h_rightOrigin, h_rightOrigin_in_arr ⟩ := h_rightOrigin
        rw [hdef, h_origin, h_id, h_content, h_rightOrigin_in_arr]
        simp [bind, Except.bind]
        grind only
    | some originId =>
      rw [h_originId] at h_origin
      simp [h_originId] at *
      generalize h_originItem : arr.find? (fun item => decide (item.id = originId)) = originItem at *
      rcases originItem with ⟨ ⟩ | ⟨ originItem ⟩ <;> simp at *
      rw [hdef, h_id, h_content]
      cases h_rightOriginId : input.rightOriginId with
      | none =>
        rw [h_rightOriginId] at h_rightOrigin
        simp [h_rightOriginId] at *
        rw [h_rightOrigin]
        simp [bind, Except.bind]; grind only
      | some rightOriginId =>
        rw [h_rightOriginId] at h_rightOrigin
        simp [h_rightOriginId] at *
        simp [bind, Except.bind]
        grind

theorem findLeftIdx_ArrSet {A : Type} [DecidableEq A] {input : IntegrateInput A} {newItem : YjsItem A} {arr : Array (YjsItem A)} {idx : ℤ} :
  uniqueId arr.toList →
  input.toItem arr = Except.ok newItem →
  findLeftIdx input.originId arr = Except.ok idx →
  ArrSet arr.toList newItem.origin := by
  intros h_unique h_newItem_def hfind
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_unique] at h_newItem_def
  grind [ArrSet]

theorem findRightIdx_ArrSet {A : Type} [DecidableEq A] {input : IntegrateInput A} {newItem : YjsItem A} {arr : Array (YjsItem A)} {idx : ℤ} :
  uniqueId arr.toList →
  input.toItem arr = Except.ok newItem →
  findRightIdx input.rightOriginId arr = Except.ok idx →
  ArrSet arr.toList newItem.rightOrigin := by
  intros h_unique h_newItem_def hfind
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_unique] at h_newItem_def
  grind [ArrSet]

theorem uniqueId_id_eq_implies_eq {A : Type} [DecidableEq A] {arr : Array (YjsItem A)} :
  uniqueId arr.toList →
  ∀ x y, x ∈ arr → y ∈ arr → x.id = y.id → x = y := by
  intros h_uniqueId x y h_x_mem h_y_mem h_eq
  simp [uniqueId] at h_uniqueId; rw [List.pairwise_iff_getElem] at h_uniqueId
  rw [Array.mem_iff_getElem] at h_x_mem
  obtain ⟨ i, h_i_lt, h_x_eq ⟩ := h_x_mem
  rw [Array.mem_iff_getElem] at h_y_mem
  obtain ⟨ j, h_j_lt, h_y_eq ⟩ := h_y_mem
  grind

theorem findLeftIdx_findPtrIdx_eq {A : Type} [DecidableEq A] {input : IntegrateInput A} {newItem : YjsItem A} {arr : Array (YjsItem A)} :
  uniqueId arr.toList →
  input.toItem arr = Except.ok newItem →
  findLeftIdx input.originId arr = findPtrIdx newItem.origin arr := by
  intros h_uniqueId h_newItem_def
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_uniqueId] at h_newItem_def
  simp [findLeftIdx, findPtrIdx]
  obtain ⟨ origin, rightOrigin, id, content, hdef, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_newItem_def
  cases h_origin_eq : input.originId with
  | none =>
    simp [h_origin_eq] at *
    grind only
  | some originId =>
    simp [h_origin_eq] at *
    obtain ⟨ originItem, h_origin_eq, h_origin_id_eq ⟩ := h_origin
    subst newItem origin; simp
    rw [Array.findIdx?_pred_eq_eq]
    intros a h_a_mem
    simp
    constructor
    . intros h_eq
      rw [Array.find?_eq_some_iff_getElem] at h_origin_id_eq
      obtain ⟨ h_id_eq, h_getElem_eq, h_lt, h_eq, h_neq ⟩ := h_origin_id_eq
      subst originItem originId
      simp at *
      have h := uniqueId_id_eq_implies_eq h_uniqueId _ _  (by simp) h_a_mem h_id_eq
      grind only
    . grind


theorem findRightIdx_findPtrIdx_eq {A : Type} [DecidableEq A] {input : IntegrateInput A} {newItem : YjsItem A} {arr : Array (YjsItem A)} :
  uniqueId arr.toList →
  input.toItem arr = Except.ok newItem →
  findRightIdx input.rightOriginId arr = findPtrIdx newItem.rightOrigin arr := by
  intros h_uniqueId h_newItem_def
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_uniqueId] at h_newItem_def
  simp [findRightIdx, findPtrIdx]
  obtain ⟨ origin, rightOrigin, id, content, hdef, h_origin, h_rightOrigin, h_id, h_content ⟩ := h_newItem_def
  cases h_origin_eq : input.rightOriginId with
  | none =>
    simp [h_origin_eq] at *
    grind only
  | some originId =>
    simp [h_origin_eq] at *
    obtain ⟨ rightOriginItem, h_origin_eq, h_origin_id_eq ⟩ := h_rightOrigin
    subst newItem rightOrigin; simp
    rw [Array.findIdx?_pred_eq_eq]
    intros a h_a_mem
    simp
    constructor
    . intros h_eq
      rw [Array.find?_eq_some_iff_getElem] at h_origin_id_eq
      obtain ⟨ h_id_eq, h_getElem_eq, h_lt, h_eq, h_neq ⟩ := h_origin_id_eq
      subst rightOriginItem originId
      simp at *
      have h := uniqueId_id_eq_implies_eq h_uniqueId _ _  (by simp) h_a_mem h_id_eq
      grind only
    . grind

omit [DecidableEq A] in theorem uniqueId_insertIdxIfInBounds_id_neq {arr : Array (YjsItem A)} {newItem : YjsItem A} :
  uniqueId (arr.insertIdxIfInBounds i newItem).toList →
  i ≤ arr.size →
  a ∈ arr → newItem.id ≠ a.id := by
  intros h_unique h_i_le_a_size h_a_mem
  simp [Array.insertIdxIfInBounds] at *
  split_ifs at h_unique
  . simp [uniqueId] at h_unique
    rw [List.pairwise_iff_getElem] at h_unique
    rw [Array.mem_iff_getElem] at h_a_mem
    obtain ⟨ j, h_j_lt, h_a_eq ⟩ := h_a_mem
    have hlength : (arr.toList.insertIdx i newItem).length = arr.size + 1 := by
      simp [h_i_le_a_size, List.length_insertIdx]
    by_cases hlt : j < i
    . have h := h_unique (if j < i then j else j + 1) i (by split <;> omega) (by omega) (by split <;> omega)
      grind only [= List.getElem_insertIdx, = Array.getElem_toList]
    . by_cases hlt : i ≤ j
      . have h := h_unique i (if j < i then j else j + 1) (by omega) (by split <;> omega) (by split <;> omega)
        grind only [= List.getElem_insertIdx, = Array.getElem_toList]
      . omega

theorem findPtrIdx_insert_some {arr other} {newItem : YjsItem A} :
  uniqueId (arr.insertIdxIfInBounds i newItem).toList
  → findPtrIdx other arr = Except.ok idx
  → findPtrIdx other (arr.insertIdxIfInBounds i newItem) = if i ≤ idx then Except.ok (idx + 1) else Except.ok idx := by
  intros hinv h_findPtrIdx_other
  by_cases hleq : ¬i ≤ arr.size
  . simp [Array.insertIdxIfInBounds, hleq] at |- hinv
    have h : idx ≤ arr.size := by
      apply findPtrIdx_le_size at h_findPtrIdx_other
      assumption
    split
    . omega
    . assumption
  . cases other with
    | first =>
      simp [findPtrIdx] at *
      cases h_findPtrIdx_other
      split; simp at *
      . omega
      . rfl
    | last =>
      simp [findPtrIdx, Array.insertIdxIfInBounds] at *
      cases h_findPtrIdx_other
      split
      . split
        . simp; rfl
        . omega
      . split
        . omega
        . omega
    | itemPtr p =>
      simp [findPtrIdx] at *
      cases heq : Array.findIdx? (fun i => decide (i = p)) arr with
      | none =>
        simp [heq] at h_findPtrIdx_other
      | some idx =>
        simp [heq] at h_findPtrIdx_other
        have hneq : newItem ≠ p := by
          intros hpeq
          have hmem : p ∈ arr := by
            rw [Array.findIdx?_eq_some_iff_getElem] at heq
            obtain ⟨ _, hgetElem, _ ⟩ := heq
            simp at *
            grind
          apply uniqueId_insertIdxIfInBounds_id_neq hinv hleq hmem (by rw [hpeq])
        rw [Array.findIdx?_insertIdxIfInBounds_some (by grind) heq]
        cases h_findPtrIdx_other
        split_ifs
        . omega
        . rfl
        . rfl
        . omega
