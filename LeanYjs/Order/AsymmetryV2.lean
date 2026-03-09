import LeanYjs.Order.TransitivityV2

variable {A : Type}

private theorem yjsLt_conflictLt_decreases_v2 {S : ItemSetV2 A}
    (inv : YjsItemSetInvariantV2 S) {x y : YjsItemV2 A} :
    S.ItemIn x ->
    S.ItemIn y ->
    ConflictLtV2' S x y ->
    ConflictLtV2' S y x ->
    ∃ x' y',
      S.RefIn x' ∧
      S.RefIn y' ∧
      inv.pairSize x' y' < inv.pairSize x.toRef y.toRef ∧
      YjsLtV2' S x' y' ∧
      YjsLtV2' S y' x' := by
  intro hx hy hxy hyx
  have hxoRef : S.RefIn x.origin := inv.origin_refIn hx
  have hyoRef : S.RefIn y.origin := inv.origin_refIn hy
  have hXOriginLt :
      inv.refSize x.origin < inv.refSize x.toRef := by
    simpa using inv.origin_size_lt_toRef_size (item := x) hx
  have hYOriginLt :
      inv.refSize y.origin < inv.refSize y.toRef := by
    simpa using inv.origin_size_lt_toRef_size (item := y) hy
  rcases hxy with ⟨ _, hxyC ⟩
  rcases hyx with ⟨ _, hyxC ⟩
  cases hxyC with
  | ltOriginDiff _ _ _ _ hx' hy' hyoLtxo _ _ _ =>
      cases hyxC with
      | ltOriginDiff _ _ _ _ hy'' hx'' hxoLtyo _ _ _ =>
          refine ⟨ x.origin, y.origin, hxoRef, hyoRef, ?_, ?_, ?_ ⟩
          · rw [YjsItemSetInvariantV2.pairSize, YjsItemSetInvariantV2.pairSize]
            rw [inv.toRef_size_eq hx, inv.toRef_size_eq hy]
            omega
          · exact ⟨ _, hxoLtyo ⟩
          · exact ⟨ _, hyoLtxo ⟩
      | ltOriginSame _ _ hy'' hx'' hOrigin _ _ hId =>
          have hlt : YjsLtV2' S x.origin x.origin := by
            simpa [hOrigin] using (show YjsLtV2' S y.origin x.origin from ⟨ _, hyoLtxo ⟩)
          refine ⟨ x.origin, x.origin, hxoRef, hxoRef, ?_, hlt, hlt ⟩
          rw [YjsItemSetInvariantV2.pairSize, YjsItemSetInvariantV2.pairSize]
          rw [inv.toRef_size_eq hx, inv.toRef_size_eq hy, hOrigin]
          omega
  | ltOriginSame _ _ hx' hy' hOrigin _ _ hId =>
      cases hyxC with
      | ltOriginDiff _ _ _ _ hy'' hx'' hxoLtyo _ _ _ =>
          have hlt : YjsLtV2' S x.origin x.origin := by
            simpa [hOrigin] using (show YjsLtV2' S x.origin y.origin from ⟨ _, hxoLtyo ⟩)
          refine ⟨ x.origin, x.origin, hxoRef, hxoRef, ?_, hlt, hlt ⟩
          rw [YjsItemSetInvariantV2.pairSize, YjsItemSetInvariantV2.pairSize]
          rw [inv.toRef_size_eq hx, inv.toRef_size_eq hy, hOrigin]
          omega
      | ltOriginSame _ _ hy'' hx'' hOrigin' _ _ hId' =>
          exact False.elim (YjsId_lt_asymm_v2 hId hId')

private theorem yjsLeq_rightOrigin_decreases_v2 {S : ItemSetV2 A}
    (inv : YjsItemSetInvariantV2 S) {x : YjsItemV2 A} {y : ItemRef} :
    S.ItemIn x ->
    S.RefIn y ->
    YjsLeqV2' S x.rightOrigin y ->
    YjsLtV2' S y x.toRef ->
    ∃ x' y',
      S.RefIn x' ∧
      S.RefIn y' ∧
      inv.pairSize x' y' < inv.pairSize x.toRef y ∧
      YjsLtV2' S x' y' ∧
      YjsLtV2' S y' x' := by
  intro hx hy hxrLeq hyx
  have hxRef : S.RefIn x.toRef := ItemSetV2.refIn_of_itemIn hx
  have hxrRef : S.RefIn x.rightOrigin := inv.rightOrigin_refIn hx
  have hxLtRight : YjsLtV2' S x.toRef x.rightOrigin := by
    exact YjsLtV2'.ltRightOrigin hx (YjsLeqV2'.leqSame _)
  have hyLtRight : YjsLtV2' S y x.rightOrigin := by
    exact inv.yjsLt_trans_v2 y x.toRef x.rightOrigin hy hxRef hxrRef hyx hxLtRight
  have hRightLt :
      inv.refSize x.rightOrigin < inv.refSize x.toRef := by
    simpa using inv.rightOrigin_size_lt_toRef_size (item := x) hx
  have hRightY :
      YjsLtV2' S x.rightOrigin y := by
    cases yjsLeqV2_imp_eq_or_yjsLtV2 hxrLeq with
    | inl hEq =>
        simpa [hEq] using hyLtRight
    | inr hLt =>
        exact hLt
  refine ⟨ x.rightOrigin, y, hxrRef, hy, ?_, hRightY, hyLtRight ⟩
  exact inv.pairSize_lt_of_left_lt hRightLt

private theorem yjsLeq_origin_decreases_v2 {S : ItemSetV2 A}
    (inv : YjsItemSetInvariantV2 S) {x : ItemRef} {y : YjsItemV2 A} :
    S.RefIn x ->
    S.ItemIn y ->
    YjsLeqV2' S x y.origin ->
    YjsLtV2' S y.toRef x ->
    ∃ x' y',
      S.RefIn x' ∧
      S.RefIn y' ∧
      inv.pairSize x' y' < inv.pairSize x y.toRef ∧
      YjsLtV2' S x' y' ∧
      YjsLtV2' S y' x' := by
  intro hx hy hxoLeq hyx
  have hyRef : S.RefIn y.toRef := ItemSetV2.refIn_of_itemIn hy
  have hyoRef : S.RefIn y.origin := inv.origin_refIn hy
  have hOriginLtY : YjsLtV2' S y.origin y.toRef := by
    exact YjsLtV2'.ltOrigin hy (YjsLeqV2'.leqSame _)
  have hOriginLtX : YjsLtV2' S y.origin x := by
    exact inv.yjsLt_trans_v2 y.origin y.toRef x hyoRef hyRef hx hOriginLtY hyx
  have hOriginLt :
      inv.refSize y.origin < inv.refSize y.toRef := by
    simpa using inv.origin_size_lt_toRef_size (item := y) hy
  have hXLtOrigin :
      YjsLtV2' S x y.origin := by
    cases yjsLeqV2_imp_eq_or_yjsLtV2 hxoLeq with
    | inl hEq =>
        simpa [hEq] using hOriginLtX
    | inr hLt =>
        exact hLt
  refine ⟨ x, y.origin, hx, hyoRef, ?_, hXLtOrigin, hOriginLtX ⟩
  exact inv.pairSize_lt_of_right_lt hOriginLt

namespace YjsItemSetInvariantV2

theorem yjsLt_asymm_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x y, S.RefIn x -> S.RefIn y ->
      YjsLtV2' S x y -> YjsLtV2' S y x -> False := by
  refine inv.pairSize_induction
    (motive := fun x y =>
      S.RefIn x -> S.RefIn y -> YjsLtV2' S x y -> YjsLtV2' S y x -> False) ?_
  intro x y ih hx hy hxy hyx
  rcases yjsLtV2'_cases S x y hxy with
    hFirst | hLast | hRight | hOrigin | hConflict
  · rcases hFirst with ⟨ hxEq, hyLast | ⟨ yid, hyEq, hyId ⟩ ⟩
    · subst hxEq hyLast
      exact YjsLtV2'.not_last_first hyx
    · have hyRef' : S.RefIn (.idRef yid) := by
        simpa [hyEq] using hy
      have hyx' : YjsLtV2' S (.idRef yid) .first := by
        simpa [hxEq, hyEq] using hyx
      exact inv.not_ref_lt_first (.idRef yid) hyRef' hyx'
  · rcases hLast with ⟨ hyEq, _ ⟩
    subst hyEq
    exact inv.not_last_lt_ref x hx hyx
  · rcases hRight with ⟨ item, hEq, hItem, hLeq ⟩
    subst hEq
    rcases yjsLeq_rightOrigin_decreases_v2 inv hItem hy hLeq hyx with
      ⟨ x', y', hx', hy', hSize, hLt1, hLt2 ⟩
    exact ih x' y' hSize hx' hy' hLt1 hLt2
  · rcases hOrigin with ⟨ item, hEq, hItem, hLeq ⟩
    subst hEq
    rcases yjsLeq_origin_decreases_v2 inv hx hItem hLeq hyx with
      ⟨ x', y', hx', hy', hSize, hLt1, hLt2 ⟩
    exact ih x' y' hSize hx' hy' hLt1 hLt2
  · rcases hConflict with ⟨ item1, item2, hxEq, hyEq, hxyConflict ⟩
    subst hxEq hyEq
    have hxItem : S.ItemIn item1 := by
      rcases hxyConflict with ⟨ _, hC ⟩
      cases hC with
      | ltOriginDiff _ _ _ _ h1 _ _ _ _ _ => exact h1
      | ltOriginSame _ _ h1 _ _ _ _ _ => exact h1
    have hyItem : S.ItemIn item2 := by
      rcases hxyConflict with ⟨ _, hC ⟩
      cases hC with
      | ltOriginDiff _ _ _ _ _ h2 _ _ _ _ => exact h2
      | ltOriginSame _ _ _ h2 _ _ _ _ => exact h2
    have ihItems :
        ∀ x' y',
          inv.pairSize x' y' <
            inv.pairSize (YjsItemV2.toRef A item1) (YjsItemV2.toRef A item2) ->
          S.RefIn x' -> S.RefIn y' ->
          YjsLtV2' S x' y' -> YjsLtV2' S y' x' -> False := by
      intro x' y' hSize hx' hy' hLt1 hLt2
      exact ih x' y'
        (by simpa [YjsItemV2.toRef] using hSize)
        hx' hy' hLt1 hLt2
    rcases yjsLtV2'_cases S item2.toRef item1.toRef hyx with
      hFirst | hLast | hRight | hOrigin | hConflict'
    · rcases hFirst with ⟨ hEq, _ ⟩
      cases hEq
    · rcases hLast with ⟨ hEq, _ ⟩
      cases hEq
    · rcases hRight with ⟨ item, hEq, hItem, hLeq ⟩
      have hItemEq : item = item2 := by
        apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hItem hyItem
        simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hEq.symm
      subst hItemEq
      rcases yjsLeq_rightOrigin_decreases_v2 inv hyItem
        (ItemSetV2.refIn_of_itemIn hxItem)
        hLeq hxy with
        ⟨ x', y', hx', hy', hSize, hLt1, hLt2 ⟩
      exact ihItems x' y'
        (by simpa [YjsItemSetInvariantV2.pairSize, Nat.add_comm] using hSize)
        hx' hy' hLt1 hLt2
    · rcases hOrigin with ⟨ item, hEq, hItem, hLeq ⟩
      have hItemEq : item = item1 := by
        apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hItem hxItem
        simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hEq.symm
      subst hItemEq
      rcases yjsLeq_origin_decreases_v2 inv
        (ItemSetV2.refIn_of_itemIn hyItem)
        hxItem hLeq hxy with
        ⟨ x', y', hx', hy', hSize, hLt1, hLt2 ⟩
      exact ihItems x' y'
        (by simpa [YjsItemSetInvariantV2.pairSize, Nat.add_comm] using hSize)
        hx' hy' hLt1 hLt2
    · rcases hConflict' with ⟨ yItem, xItem, hyEq', hxEq', hyxConflict ⟩
      have hyItemEq : yItem = item2 := by
        have hyItemIn : S.ItemIn yItem := by
          rcases hyxConflict with ⟨ _, hC ⟩
          cases hC with
          | ltOriginDiff _ _ _ _ h1 _ _ _ _ _ => exact h1
          | ltOriginSame _ _ h1 _ _ _ _ _ => exact h1
        apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hyItemIn hyItem
        simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hyEq'.symm
      have hxItemEq : xItem = item1 := by
        have hxItemIn' : S.ItemIn xItem := by
          rcases hyxConflict with ⟨ _, hC ⟩
          cases hC with
          | ltOriginDiff _ _ _ _ _ h2 _ _ _ _ => exact h2
          | ltOriginSame _ _ _ h2 _ _ _ _ => exact h2
        apply ItemSetV2.item_eq_of_itemIn_of_id_eq (S := S) hxItemIn' hxItem
        simpa [YjsItemV2.toRef] using congrArg ItemRef.toOptionId hxEq'.symm
      subst hyItemEq hxItemEq
      rcases yjsLt_conflictLt_decreases_v2 inv hxItem hyItem hxyConflict hyxConflict with
        ⟨ x', y', hx', hy', hSize, hLt1, hLt2 ⟩
      exact ihItems x' y' hSize hx' hy' hLt1 hLt2

theorem yjsLt_of_not_leq_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x y, S.RefIn x -> S.RefIn y ->
      YjsLtV2' S x y -> ¬ YjsLeqV2' S y x := by
  intro x y hx hy hxy hyx
  cases yjsLeqV2_imp_eq_or_yjsLtV2 hyx with
  | inl hEq =>
      have hxx : YjsLtV2' S x x := by
        simpa [hEq] using hxy
      exact inv.yjsLt_asymm_v2 x x hx hx hxx hxx
  | inr hLt =>
      exact inv.yjsLt_asymm_v2 x y hx hy hxy hLt

end YjsItemSetInvariantV2
