import LeanYjs.Order.TotalityV2

variable {A : Type}

theorem YjsId_lt_asymm_v2 {id1 id2 : YjsId} :
    id1 < id2 -> Not (id2 < id1) := by
  intro hLt hLt'
  obtain ⟨ clientId1, clock1 ⟩ := id1
  obtain ⟨ clientId2, clock2 ⟩ := id2
  simp only [LT.lt] at *
  simp at *
  unfold ClientId at *
  split at hLt
  · split at hLt'
    · omega
    · omega
  · split at hLt'
    · omega
    · omega

namespace YjsLtV2'

theorem not_first_first {S : ItemSetV2 A} :
    Not (YjsLtV2' S .first .first) := by
  intro hLt
  rcases yjsLtV2'_cases S .first .first hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · rcases hFirst with ⟨ _, hLast | ⟨ _, hEq, _ ⟩ ⟩
    · cases hLast
    · cases hEq
  · cases hLast.1
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hConflict with ⟨ _, _, hEq, _, _ ⟩
    cases hEq

theorem not_last_last {S : ItemSetV2 A} :
    Not (YjsLtV2' S .last .last) := by
  intro hLt
  rcases yjsLtV2'_cases S .last .last hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · cases hFirst.1
  · rcases hLast with ⟨ _, hFirst | ⟨ _, hEq, _ ⟩ ⟩
    · cases hFirst
    · cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hConflict with ⟨ _, _, hEq, _, _ ⟩
    cases hEq

theorem not_last_first {S : ItemSetV2 A} :
    Not (YjsLtV2' S .last .first) := by
  intro hLt
  rcases yjsLtV2'_cases S .last .first hLt with
    hFirst | hLast | hItem | hItem | hConflict
  · cases hFirst.1
  · cases hLast.1
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hItem with ⟨ _, hEq, _, _ ⟩
    cases hEq
  · rcases hConflict with ⟨ _, _, hEq, _, _ ⟩
    cases hEq

end YjsLtV2'

namespace YjsItemSetInvariantV2

theorem not_ref_lt_first {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x, S.RefIn x -> ¬ YjsLtV2' S x .first := by
  have hMain :
      ∀ x y, y = .first -> S.RefIn x -> S.RefIn y -> ¬ YjsLtV2' S x y := by
    refine inv.pairDepth_induction
      (motive := fun x y => y = .first -> S.RefIn x -> S.RefIn y -> ¬ YjsLtV2' S x y) ?_
    intro x y ih hyEq hx hy hLt
    subst hyEq
    cases x with
    | first =>
        exact YjsLtV2'.not_first_first hLt
    | last =>
        exact YjsLtV2'.not_last_first hLt
    | idRef id =>
        rcases yjsLtV2'_cases S (.idRef id) .first hLt with
          hFirst | hLast | hItem | hItem | hConflict
        · rcases hFirst with ⟨ hEq, _ ⟩
          cases hEq
        · cases hLast.1
        · rcases hItem with ⟨ item, hEq, hItem, hLeq ⟩
          cases hEq
          cases yjsLeqV2_imp_eq_or_yjsLtV2 hLeq with
          | inl hRightEq =>
              have hOriginLtDepth :
                  inv.refDepth item.origin < inv.refDepth item.toRef := by
                simpa using inv.origin_depth_lt_toRef_depth (item := item) hItem
              have hOriginLtFirst : YjsLtV2' S item.origin .first := by
                obtain ⟨ h, hLt' ⟩ := inv.origin_lt_rightOrigin hItem
                simpa [YjsItemV2.toRef, hRightEq] using
                  (show YjsLtV2' S item.origin item.rightOrigin from ⟨ h, hLt' ⟩)
              exact ih item.origin .first
                (by
                  simpa [YjsItemSetInvariantV2.pairDepth] using
                    inv.pairDepth_lt_of_left_lt (z := .first) hOriginLtDepth)
                rfl
                (inv.origin_refIn hItem)
                trivial
                hOriginLtFirst
          | inr hRightLt =>
              have hRightLtDepth :
                  inv.refDepth item.rightOrigin < inv.refDepth item.toRef := by
                simpa using inv.rightOrigin_depth_lt_toRef_depth (item := item) hItem
              exact ih item.rightOrigin .first
                (by
                  simpa [YjsItemSetInvariantV2.pairDepth] using
                    inv.pairDepth_lt_of_left_lt (z := .first) hRightLtDepth)
                rfl
                (inv.rightOrigin_refIn hItem)
                trivial
                hRightLt
        · rcases hItem with ⟨ item, hEq, _, _ ⟩
          cases hEq
        · rcases hConflict with ⟨ _, _, _, hEq, _ ⟩
          cases hEq
  intro x hx hLt
  exact hMain x .first rfl hx trivial hLt

theorem not_last_lt_ref {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    ∀ x, S.RefIn x -> ¬ YjsLtV2' S .last x := by
  have hMain :
      ∀ x y, x = .last -> S.RefIn x -> S.RefIn y -> ¬ YjsLtV2' S x y := by
    refine inv.pairDepth_induction
      (motive := fun x y => x = .last -> S.RefIn x -> S.RefIn y -> ¬ YjsLtV2' S x y) ?_
    intro x y ih hxEq hx hy hLt
    subst hxEq
    cases y with
    | first =>
        exact YjsLtV2'.not_last_first hLt
    | last =>
        exact YjsLtV2'.not_last_last hLt
    | idRef id =>
        rcases yjsLtV2'_cases S .last (.idRef id) hLt with
          hFirst | hLast | hItem | hItem | hConflict
        · cases hFirst.1
        · rcases hLast with ⟨ hEq, _ ⟩
          cases hEq
        · rcases hItem with ⟨ item, hEq, _, _ ⟩
          cases hEq
        · rcases hItem with ⟨ item, hEq, hItem, hLeq ⟩
          cases hEq
          cases yjsLeqV2_imp_eq_or_yjsLtV2 hLeq with
          | inl hOriginEq =>
              have hRightLtDepth :
                  inv.refDepth item.rightOrigin < inv.refDepth item.toRef := by
                simpa using inv.rightOrigin_depth_lt_toRef_depth (item := item) hItem
              have hLastLtRight : YjsLtV2' S .last item.rightOrigin := by
                obtain ⟨ h, hLt' ⟩ := inv.origin_lt_rightOrigin hItem
                simpa [YjsItemV2.toRef, hOriginEq] using
                  (show YjsLtV2' S item.origin item.rightOrigin from ⟨ h, hLt' ⟩)
              exact ih .last item.rightOrigin
                (by
                  simpa [YjsItemSetInvariantV2.pairDepth] using
                    inv.pairDepth_lt_of_right_lt (z := .last) hRightLtDepth)
                rfl
                trivial
                (inv.rightOrigin_refIn hItem)
                hLastLtRight
          | inr hLastLtOrigin =>
              have hOriginLtDepth :
                  inv.refDepth item.origin < inv.refDepth item.toRef := by
                simpa using inv.origin_depth_lt_toRef_depth (item := item) hItem
              exact ih .last item.origin
                (by
                  simpa [YjsItemSetInvariantV2.pairDepth] using
                    inv.pairDepth_lt_of_right_lt (z := .last) hOriginLtDepth)
                rfl
                trivial
                (inv.origin_refIn hItem)
                hLastLtOrigin
        · rcases hConflict with ⟨ item1, _, hEq, _, _ ⟩
          cases hEq
  intro x hx hLt
  exact hMain .last x rfl trivial hx hLt

end YjsItemSetInvariantV2
