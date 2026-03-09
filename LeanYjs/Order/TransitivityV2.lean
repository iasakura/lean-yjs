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

private theorem conflictLtV2_trans_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {x y z : YjsItemV2 A}
    (ih : ∀ x' y' z',
      inv.tripleSize x' y' z' < inv.tripleSize x.toRef y.toRef z.toRef ->
      S.RefIn x' -> S.RefIn y' -> S.RefIn z' ->
      YjsLtV2' S x' y' -> YjsLtV2' S y' z' -> YjsLtV2' S x' z') :
    S.ItemIn x ->
    S.ItemIn y ->
    S.ItemIn z ->
    ConflictLtV2' S x y ->
    ConflictLtV2' S y z ->
    YjsLtV2' S x.toRef z.toRef := by
  intro hx hy hz hxy hyz
  have hxRef : S.RefIn x.toRef := ItemSetV2.refIn_of_itemIn hx
  have hyRef : S.RefIn y.toRef := ItemSetV2.refIn_of_itemIn hy
  have hzRef : S.RefIn z.toRef := ItemSetV2.refIn_of_itemIn hz
  have hxoRef : S.RefIn x.origin := inv.origin_refIn hx
  have hxrRef : S.RefIn x.rightOrigin := inv.rightOrigin_refIn hx
  have hyoRef : S.RefIn y.origin := inv.origin_refIn hy
  have hyrRef : S.RefIn y.rightOrigin := inv.rightOrigin_refIn hy
  have hzoRef : S.RefIn z.origin := inv.origin_refIn hz
  have hzrRef : S.RefIn z.rightOrigin := inv.rightOrigin_refIn hz

  have hXOriginLt :
      inv.refSize x.origin < inv.refSize x.toRef := by
    simpa using inv.origin_size_lt_toRef_size (item := x) hx
  have hYOriginLt :
      inv.refSize y.origin < inv.refSize y.toRef := by
    simpa using inv.origin_size_lt_toRef_size (item := y) hy
  have hZOriginLt :
      inv.refSize z.origin < inv.refSize z.toRef := by
    simpa using inv.origin_size_lt_toRef_size (item := z) hz
  have hZRightLt :
      inv.refSize z.rightOrigin < inv.refSize z.toRef := by
    simpa using inv.rightOrigin_size_lt_toRef_size (item := z) hz

  have hxrTotal :
      YjsLeqV2' S x.rightOrigin z.toRef ∨
        YjsLtV2' S z.toRef x.rightOrigin := by
    exact inv.yjsLeq_or_yjsLt x.rightOrigin z.toRef hxrRef hzRef
  have hzoTotal :
      YjsLeqV2' S x.toRef z.origin ∨
        YjsLtV2' S z.origin x.toRef := by
    exact inv.yjsLeq_or_yjsLt x.toRef z.origin hxRef hzoRef

  have hyzr : YjsLtV2' S y.toRef z.rightOrigin := by
    exact conflictLtV2_x_lt_y_rightOrigin hyz
  have hxoy : YjsLtV2' S x.origin y.toRef := by
    exact conflictLtV2_x_origin_lt_y hxy

  have hMeasureXZR :
      inv.tripleSize x.toRef y.toRef z.rightOrigin <
        inv.tripleSize x.toRef y.toRef z.toRef := by
    exact inv.tripleSize_lt_of_right_lt hZRightLt
  have hltXZR : YjsLtV2' S x.toRef z.rightOrigin := by
    exact ih x.toRef y.toRef z.rightOrigin hMeasureXZR hxRef hyRef hzrRef
      (YjsLtV2'.ltConflict hxy) hyzr

  have hMeasureXOZ :
      inv.tripleSize x.origin y.toRef z.toRef <
        inv.tripleSize x.toRef y.toRef z.toRef := by
    exact inv.tripleSize_lt_of_left_lt hXOriginLt
  have hltXOZ : YjsLtV2' S x.origin z.toRef := by
    exact ih x.origin y.toRef z.toRef hMeasureXOZ hxoRef hyRef hzRef
      hxoy (YjsLtV2'.ltConflict hyz)

  cases hxrTotal with
  | inl hxrLeq =>
      exact YjsLtV2'.ltRightOrigin hx hxrLeq
  | inr hzLtXR =>
      cases hzoTotal with
      | inl hxLeqZO =>
          exact YjsLtV2'.ltOrigin hz hxLeqZO
      | inr hzOLtX =>
          rcases hxy with ⟨ _, hxyC ⟩
          rcases hyz with ⟨ _, hyzC ⟩
          cases hxyC with
          | ltOriginDiff _ _ _ _ hx' hy' hYoLtXo _ _ _ =>
              cases hyzC with
              | ltOriginDiff _ _ _ _ hy'' hz' hZoLtYo _ _ _ =>
                  have hMeasureZOYOXO :
                      inv.tripleSize z.origin y.origin x.origin <
                        inv.tripleSize x.toRef y.toRef z.toRef := by
                    simpa [YjsItemSetInvariantV2.tripleSize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                      using Nat.add_lt_add (Nat.add_lt_add hZOriginLt hYOriginLt) hXOriginLt
                  have hZoLtXo : YjsLtV2' S z.origin x.origin := by
                    exact ih z.origin y.origin x.origin hMeasureZOYOXO hzoRef hyoRef hxoRef
                      (by exact ⟨ _, hZoLtYo ⟩) (by exact ⟨ _, hYoLtXo ⟩)
                  have hConflict : ConflictLtV2' S x z := by
                    apply ConflictLtV2'.ltOriginDiff
                    · exact hx
                    · exact hz
                    · exact hZoLtXo
                    · exact hltXZR
                    · exact hltXOZ
                    · exact hzLtXR
                  exact YjsLtV2'.ltConflict hConflict
              | ltOriginSame _ _ hy'' hz' hOriginYZ _ _ hIdYZ =>
                  have hZoLtXo : YjsLtV2' S z.origin x.origin := by
                    simpa [hOriginYZ] using (show YjsLtV2' S y.origin x.origin from ⟨ _, hYoLtXo ⟩)
                  have hConflict : ConflictLtV2' S x z := by
                    apply ConflictLtV2'.ltOriginDiff
                    · exact hx
                    · exact hz
                    · exact hZoLtXo
                    · exact hltXZR
                    · exact hltXOZ
                    · exact hzLtXR
                  exact YjsLtV2'.ltConflict hConflict
          | ltOriginSame _ _ hx' hy' hOriginXY _ _ hIdXY =>
              cases hyzC with
              | ltOriginDiff _ _ _ _ hy'' hz' hZoLtYo _ _ _ =>
                  have hZoLtXo : YjsLtV2' S z.origin x.origin := by
                    simpa [hOriginXY] using (show YjsLtV2' S z.origin y.origin from ⟨ _, hZoLtYo ⟩)
                  have hConflict : ConflictLtV2' S x z := by
                    apply ConflictLtV2'.ltOriginDiff
                    · exact hx
                    · exact hz
                    · exact hZoLtXo
                    · exact hltXZR
                    · exact hltXOZ
                    · exact hzLtXR
                  exact YjsLtV2'.ltConflict hConflict
              | ltOriginSame _ _ hy'' hz' hOriginYZ _ _ hIdYZ =>
                  have hOriginXZ : x.origin = z.origin := by
                    rw [hOriginXY, hOriginYZ]
                  have hIdXZ : x.id < z.id := YjsId_lt_trans_v2 hIdXY hIdYZ
                  have hConflict : ConflictLtV2' S x z := by
                    apply ConflictLtV2'.ltOriginSame
                    · exact hx
                    · exact hz
                    · exact hOriginXZ
                    · exact hltXZR
                    · exact hzLtXR
                    · exact hIdXZ
                  exact YjsLtV2'.ltConflict hConflict

namespace YjsItemSetInvariantV2

theorem yjsLt_trans_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x y z, S.RefIn x -> S.RefIn y -> S.RefIn z ->
      YjsLtV2' S x y -> YjsLtV2' S y z -> YjsLtV2' S x z := by
  refine inv.tripleSize_induction
    (motive := fun x y z =>
      S.RefIn x -> S.RefIn y -> S.RefIn z ->
        YjsLtV2' S x y -> YjsLtV2' S y z -> YjsLtV2' S x z) ?_
  intro x y z ih hx hy hz hxy hyz
  cases x with
  | first =>
      cases y with
      | first =>
          exact False.elim (YjsLtV2'.not_first_first hxy)
      | last =>
          exact False.elim (inv.not_last_lt_ref z hz hyz)
      | idRef yid =>
          cases z with
          | first =>
              exact False.elim (inv.not_ref_lt_first (.idRef yid) hy hyz)
          | last =>
              exact YjsLtV2'.first_lt_last
          | idRef zid =>
              exact YjsLtV2'.first_lt_idRef hz
  | last =>
      exact False.elim (inv.not_last_lt_ref y hy hxy)
  | idRef xid =>
      cases y with
      | first =>
          exact False.elim (inv.not_ref_lt_first (.idRef xid) hx hxy)
      | last =>
          exact False.elim (inv.not_last_lt_ref z hz hyz)
      | idRef yid =>
          cases z with
          | first =>
              exact False.elim (inv.not_ref_lt_first (.idRef yid) hy hyz)
          | last =>
              exact YjsLtV2'.idRef_lt_last hx
          | idRef zid =>
              rcases itemIn_of_refIn_idRef_local (S := S) hx with ⟨ xItem, hxItem, hxId ⟩
              rcases itemIn_of_refIn_idRef_local (S := S) hy with ⟨ yItem, hyItem, hyId ⟩
              rcases itemIn_of_refIn_idRef_local (S := S) hz with ⟨ zItem, hzItem, hzId ⟩

              have hxyItem : YjsLtV2' S xItem.toRef yItem.toRef := by
                simpa [YjsItemV2.toRef, hxId, hyId] using hxy
              have hyzItem : YjsLtV2' S yItem.toRef zItem.toRef := by
                simpa [YjsItemV2.toRef, hyId, hzId] using hyz

              have hxRef : S.RefIn xItem.toRef := ItemSetV2.refIn_of_itemIn hxItem
              have hyRef : S.RefIn yItem.toRef := ItemSetV2.refIn_of_itemIn hyItem
              have hzRef : S.RefIn zItem.toRef := ItemSetV2.refIn_of_itemIn hzItem
              have hxrRef : S.RefIn xItem.rightOrigin := inv.rightOrigin_refIn hxItem
              have hyoRef : S.RefIn yItem.origin := inv.origin_refIn hyItem
              have hyrRef : S.RefIn yItem.rightOrigin := inv.rightOrigin_refIn hyItem
              have hzoRef : S.RefIn zItem.origin := inv.origin_refIn hzItem

              have hXRightLt :
                  inv.refSize xItem.rightOrigin < inv.refSize xItem.toRef := by
                simpa using inv.rightOrigin_size_lt_toRef_size (item := xItem) hxItem
              have hYOriginLt :
                  inv.refSize yItem.origin < inv.refSize yItem.toRef := by
                simpa using inv.origin_size_lt_toRef_size (item := yItem) hyItem
              have hYRightLt :
                  inv.refSize yItem.rightOrigin < inv.refSize yItem.toRef := by
                simpa using inv.rightOrigin_size_lt_toRef_size (item := yItem) hyItem
              have hZOriginLt :
                  inv.refSize zItem.origin < inv.refSize zItem.toRef := by
                simpa using inv.origin_size_lt_toRef_size (item := zItem) hzItem

              have hOriginRight : YjsLtV2' S yItem.origin yItem.rightOrigin := by
                rcases inv.origin_lt_rightOrigin hyItem with ⟨ h, hLt' ⟩
                exact ⟨ h, hLt' ⟩

              have ihItems :
                  ∀ x' y' z',
                    inv.tripleSize x' y' z' <
                      inv.tripleSize xItem.toRef yItem.toRef zItem.toRef ->
                    S.RefIn x' -> S.RefIn y' -> S.RefIn z' ->
                    YjsLtV2' S x' y' -> YjsLtV2' S y' z' -> YjsLtV2' S x' z' := by
                intro x' y' z' hMeasure hx' hy' hz' hlt1 hlt2
                exact ih x' y' z'
                  (by simpa [YjsItemV2.toRef, hxId, hyId, hzId] using hMeasure)
                  hx' hy' hz' hlt1 hlt2

              have hxyCases := lt_cases_idRef_idRef (S := S) hxItem hyItem hxyItem
              have hyzCases := lt_cases_idRef_idRef (S := S) hyItem hzItem hyzItem

              cases hxyCases with
              | inl hxrLeq =>
                  cases yjsLeqV2_imp_eq_or_yjsLtV2 hxrLeq with
                  | inl hEq =>
                      have hLeq : YjsLeqV2' S xItem.rightOrigin zItem.toRef := by
                        simpa [hEq] using (YjsLeqV2'.leqLt hyzItem)
                      have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                        exact YjsLtV2'.ltRightOrigin hxItem hLeq
                      simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                  | inr hxrLtY =>
                      have hMeasure :
                          inv.tripleSize xItem.rightOrigin yItem.toRef zItem.toRef <
                            inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                        exact inv.tripleSize_lt_of_left_lt hXRightLt
                      have hlt : YjsLtV2' S xItem.rightOrigin zItem.toRef := by
                        exact ihItems xItem.rightOrigin yItem.toRef zItem.toRef
                          hMeasure hxrRef hyRef hzRef hxrLtY hyzItem
                      have hlt' : YjsLtV2' S xItem.toRef zItem.toRef := by
                        exact YjsLtV2'.ltRightOrigin hxItem (YjsLeqV2'.leqLt hlt)
                      simpa [YjsItemV2.toRef, hxId, hzId] using hlt'
              | inr hxyRest =>
                  cases hxyRest with
                  | inl hxoLeq =>
                      cases hyzCases with
                      | inl hyrLeq =>
                          cases yjsLeqV2_imp_eq_or_yjsLtV2 hxoLeq with
                          | inl hEqXY =>
                              cases yjsLeqV2_imp_eq_or_yjsLtV2 hyrLeq with
                              | inl hEqYZ =>
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    rw [hEqXY, ← hEqYZ]
                                    exact hOriginRight
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                              | inr hyrLtZ =>
                                  have hMeasure :
                                      inv.tripleSize xItem.toRef yItem.rightOrigin zItem.toRef <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    exact inv.tripleSize_lt_of_middle_lt hYRightLt
                                  have hXRight : YjsLtV2' S xItem.toRef yItem.rightOrigin := by
                                    rw [hEqXY]
                                    exact hOriginRight
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact ihItems xItem.toRef yItem.rightOrigin zItem.toRef
                                      hMeasure hxRef hyrRef hzRef hXRight hyrLtZ
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                          | inr hXoLtY =>
                              cases yjsLeqV2_imp_eq_or_yjsLtV2 hyrLeq with
                              | inl hEqYZ =>
                                  have hYoLtZ : YjsLtV2' S yItem.origin zItem.toRef := by
                                    simpa [hEqYZ] using hOriginRight
                                  have hMeasure :
                                      inv.tripleSize xItem.toRef yItem.origin zItem.toRef <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    exact inv.tripleSize_lt_of_middle_lt hYOriginLt
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact ihItems xItem.toRef yItem.origin zItem.toRef
                                      hMeasure hxRef hyoRef hzRef hXoLtY hYoLtZ
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                              | inr hyrLtZ =>
                                  have hMeasureYoYrZ :
                                      inv.tripleSize yItem.origin yItem.rightOrigin zItem.toRef <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    rw [YjsItemSetInvariantV2.tripleSize,
                                      YjsItemSetInvariantV2.tripleSize]
                                    rw [inv.toRef_size_eq hyItem]
                                    omega
                                  have hYoLtZ : YjsLtV2' S yItem.origin zItem.toRef := by
                                    exact ihItems yItem.origin yItem.rightOrigin zItem.toRef
                                      hMeasureYoYrZ hyoRef hyrRef hzRef hOriginRight hyrLtZ
                                  have hMeasure :
                                      inv.tripleSize xItem.toRef yItem.origin zItem.toRef <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    exact inv.tripleSize_lt_of_middle_lt hYOriginLt
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact ihItems xItem.toRef yItem.origin zItem.toRef
                                      hMeasure hxRef hyoRef hzRef hXoLtY hYoLtZ
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                      | inr hyzRest =>
                          cases hyzRest with
                          | inl hyzoLeq =>
                              cases yjsLeqV2_imp_eq_or_yjsLtV2 hyzoLeq with
                              | inl hEq =>
                                  have hLeq : YjsLeqV2' S xItem.toRef zItem.origin := by
                                    rw [← hEq]
                                    exact YjsLeqV2'.leqLt hxyItem
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact YjsLtV2'.ltOrigin hzItem hLeq
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                              | inr hyLtZo =>
                                  have hMeasure :
                                      inv.tripleSize xItem.toRef yItem.toRef zItem.origin <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    exact inv.tripleSize_lt_of_right_lt hZOriginLt
                                  have hXLtZo : YjsLtV2' S xItem.toRef zItem.origin := by
                                    exact ihItems xItem.toRef yItem.toRef zItem.origin
                                      hMeasure hxRef hyRef hzoRef hxyItem hyLtZo
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact YjsLtV2'.ltOrigin hzItem (YjsLeqV2'.leqLt hXLtZo)
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                          | inr hYZConflict =>
                              have hYoLtZ : YjsLtV2' S yItem.origin zItem.toRef := by
                                exact conflictLtV2_x_origin_lt_y hYZConflict
                              cases yjsLeqV2_imp_eq_or_yjsLtV2 hxoLeq with
                              | inl hEq =>
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    rw [hEq]
                                    exact hYoLtZ
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                              | inr hXoLtY =>
                                  have hMeasure :
                                      inv.tripleSize xItem.toRef yItem.origin zItem.toRef <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    exact inv.tripleSize_lt_of_middle_lt hYOriginLt
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact ihItems xItem.toRef yItem.origin zItem.toRef
                                      hMeasure hxRef hyoRef hzRef hXoLtY hYoLtZ
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                  | inr hXYConflict =>
                      cases hyzCases with
                      | inl hyrLeq =>
                          have hXLtYr : YjsLtV2' S xItem.toRef yItem.rightOrigin := by
                            exact conflictLtV2_x_lt_y_rightOrigin hXYConflict
                          cases yjsLeqV2_imp_eq_or_yjsLtV2 hyrLeq with
                          | inl hEq =>
                              simpa [YjsItemV2.toRef, hxId, hzId, hEq] using hXLtYr
                          | inr hyrLtZ =>
                              have hMeasure :
                                  inv.tripleSize xItem.toRef yItem.rightOrigin zItem.toRef <
                                    inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                exact inv.tripleSize_lt_of_middle_lt hYRightLt
                              have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                exact ihItems xItem.toRef yItem.rightOrigin zItem.toRef
                                  hMeasure hxRef hyrRef hzRef hXLtYr hyrLtZ
                              simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                      | inr hyzRest =>
                          cases hyzRest with
                          | inl hyzoLeq =>
                              cases yjsLeqV2_imp_eq_or_yjsLtV2 hyzoLeq with
                              | inl hEq =>
                                  have hLeq : YjsLeqV2' S xItem.toRef zItem.origin := by
                                    rw [← hEq]
                                    exact YjsLeqV2'.leqLt hxyItem
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact YjsLtV2'.ltOrigin hzItem hLeq
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                              | inr hyLtZo =>
                                  have hMeasure :
                                      inv.tripleSize xItem.toRef yItem.toRef zItem.origin <
                                        inv.tripleSize xItem.toRef yItem.toRef zItem.toRef := by
                                    exact inv.tripleSize_lt_of_right_lt hZOriginLt
                                  have hXLtZo : YjsLtV2' S xItem.toRef zItem.origin := by
                                    exact ihItems xItem.toRef yItem.toRef zItem.origin
                                      hMeasure hxRef hyRef hzoRef hxyItem hyLtZo
                                  have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                    exact YjsLtV2'.ltOrigin hzItem (YjsLeqV2'.leqLt hXLtZo)
                                  simpa [YjsItemV2.toRef, hxId, hzId] using hlt
                          | inr hYZConflict =>
                              have hlt : YjsLtV2' S xItem.toRef zItem.toRef := by
                                exact conflictLtV2_trans_v2 inv ihItems
                                  hxItem hyItem hzItem hXYConflict hYZConflict
                              simpa [YjsItemV2.toRef, hxId, hzId] using hlt

theorem yjsLeq_lt_trans_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x y z, S.RefIn x -> S.RefIn y -> S.RefIn z ->
      YjsLeqV2' S x y -> YjsLtV2' S y z -> YjsLtV2' S x z := by
  intro x y z hx hy hz hxy hyz
  cases yjsLeqV2_imp_eq_or_yjsLtV2 hxy with
  | inl hEq =>
      simpa [hEq] using hyz
  | inr hLt =>
      exact inv.yjsLt_trans_v2 x y z hx hy hz hLt hyz

theorem yjsLt_leq_trans_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x y z, S.RefIn x -> S.RefIn y -> S.RefIn z ->
      YjsLtV2' S x y -> YjsLeqV2' S y z -> YjsLtV2' S x z := by
  intro x y z hx hy hz hxy hyz
  cases yjsLeqV2_imp_eq_or_yjsLtV2 hyz with
  | inl hEq =>
      simpa [hEq] using hxy
  | inr hLt =>
      exact inv.yjsLt_trans_v2 x y z hx hy hz hxy hLt

theorem yjsLeq_trans_v2 {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x y z, S.RefIn x -> S.RefIn y -> S.RefIn z ->
      YjsLeqV2' S x y -> YjsLeqV2' S y z -> YjsLeqV2' S x z := by
  intro x y z hx hy hz hxy hyz
  cases yjsLeqV2_imp_eq_or_yjsLtV2 hxy with
  | inl hEq =>
      simpa [hEq] using hyz
  | inr hLt =>
      exact YjsLeqV2'.leqLt (inv.yjsLt_leq_trans_v2 x y z hx hy hz hLt hyz)

end YjsItemSetInvariantV2
