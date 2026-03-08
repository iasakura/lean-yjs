import LeanYjs.Order.BoundaryV2
import LeanYjs.Order.SizeV2

variable {A : Type}

private theorem itemIn_of_refIn_idRef_local {S : ItemSetV2 A} {id : YjsId} :
    S.RefIn (.idRef id) -> Exists fun item => S.ItemIn item ∧ item.id = id := by
  intro hRef
  rcases hRef with ⟨ item, hLookup ⟩
  refine ⟨ item, ?_, S.lookup_sound hLookup ⟩
  simpa [S.lookup_sound hLookup] using hLookup

private theorem lt_cases_idRef_idRef {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    S.ItemIn x ->
    S.ItemIn y ->
    YjsLtV2' S x.toRef y.toRef ->
      YjsLeqV2' S x.rightOrigin y.toRef ∨
      YjsLeqV2' S x.toRef y.origin ∨
      ConflictLtV2' S x y := by
  intro hItemX hItemY hLt
  rcases yjsLtV2'_cases S x.toRef y.toRef hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · cases hFirst.1
  · cases hLast.1
  · rcases hItem with ⟨ item, hEq, hItem, hLeq ⟩
    have hItemEq : item = x := by
      apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hItem hItemX
      simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hEq.symm
    subst hItemEq
    exact Or.inl hLeq
  · rcases hItem with ⟨ item, hEq, hItem, hLeq ⟩
    have hItemEq : item = y := by
      apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hItem hItemY
      simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hEq.symm
    subst hItemEq
    exact Or.inr (Or.inl hLeq)
  · rcases hConflict with ⟨ item1, item2, hEq1, hEq2, hConflict ⟩
    have hItem1In : S.ItemIn item1 := by
      rcases hConflict with ⟨ _, hC ⟩
      cases hC with
      | ltOriginDiff _ _ _ _ hItem1 _ _ _ _ _ =>
          exact hItem1
      | ltOriginSame _ _ hItem1 _ _ _ _ _ =>
          exact hItem1
    have hItem2In : S.ItemIn item2 := by
      rcases hConflict with ⟨ _, hC ⟩
      cases hC with
      | ltOriginDiff _ _ _ _ _ hItem2 _ _ _ _ =>
          exact hItem2
      | ltOriginSame _ _ _ hItem2 _ _ _ _ =>
          exact hItem2
    have hItemEq1 : item1 = x := by
      apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hItem1In hItemX
      simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hEq1.symm
    have hItemEq2 : item2 = y := by
      apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hItem2In hItemY
      simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hEq2.symm
    subst hItemEq1 hItemEq2
    exact Or.inr (Or.inr hConflict)

theorem YjsId_lt_trans_v2 {x y z : YjsId} :
    x < y -> y < z -> x < z := by
  intro hxy hyz
  obtain ⟨ xClientId, xClock ⟩ := x
  obtain ⟨ yClientId, yClock ⟩ := y
  obtain ⟨ zClientId, zClock ⟩ := z
  simp only [LT.lt] at *
  simp at *
  unfold ClientId at *
  split at hxy
  · subst xClientId
    split at hyz
    · subst yClientId
      simp
      omega
    · split
      · omega
      · omega
  · split at hyz
    · subst zClientId
      split
      · omega
      · omega
    · split
      · omega
      · omega

theorem conflictLtV2_x_origin_lt_y {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S x.origin y.toRef := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ _ hItemY _ _ hlt3 _ =>
      exact ⟨ _, hlt3 ⟩
  | ltOriginSame _ _ _ hItemY hOrigin _ _ _ =>
      simpa [YjsItemV2.toRef, hOrigin] using
        (YjsLtV2'.ltOrigin hItemY (YjsLeqV2'.leqSame y.origin))

theorem conflictLtV2_y_origin_lt_x {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S y.origin x.toRef := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ hItemX _ hlt1 _ _ _ =>
      exact YjsLtV2'.ltOrigin hItemX (YjsLeqV2'.leqLt ⟨ _, hlt1 ⟩)
  | ltOriginSame _ _ hItemX _ hOrigin _ _ _ =>
      simpa [YjsItemV2.toRef, hOrigin] using
        (YjsLtV2'.ltOrigin hItemX (YjsLeqV2'.leqSame x.origin))

theorem conflictLtV2_y_lt_x_rightOrigin {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S y.toRef x.rightOrigin := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ _ _ _ _ _ hlt4 =>
      exact ⟨ _, hlt4 ⟩
  | ltOriginSame _ _ _ _ _ _ hlt2 _ =>
      exact ⟨ _, hlt2 ⟩

theorem conflictLtV2_x_lt_y_rightOrigin {S : ItemSetV2 A} {x y : YjsItemV2 A} :
    ConflictLtV2' S x y ->
    YjsLtV2' S x.toRef y.rightOrigin := by
  intro hLt
  rcases hLt with ⟨ _, hLt ⟩
  cases hLt with
  | ltOriginDiff _ _ _ _ _ _ _ hlt2 _ _ =>
      exact ⟨ _, hlt2 ⟩
  | ltOriginSame _ _ _ _ _ hlt1 _ _ =>
      exact ⟨ _, hlt1 ⟩
