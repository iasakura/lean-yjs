import LeanYjs.ClientId
import LeanYjs.Order.MeasureV2

variable {A : Type}

private theorem itemIn_of_refIn_idRef_local {S : ItemSetV2 A} {id : YjsId} :
    S.RefIn (.idRef id) -> Exists fun item => S.ItemIn item ∧ item.id = id := by
  intro hRef
  rcases hRef with ⟨ item, hLookup ⟩
  refine ⟨ item, ?_, S.lookup_sound hLookup ⟩
  simpa [S.lookup_sound hLookup] using hLookup

theorem YjsId_lt_total {x y : YjsId} :
    x < y ∨ y < x ∨ x = y := by
  obtain ⟨ xClientId, xClock ⟩ := x
  obtain ⟨ yClientId, yClock ⟩ := y
  simp only [LT.lt]
  unfold ClientId at *
  split
  · rw [beq_iff_eq] at *
    subst xClientId
    rw [beq_self_eq_true]
    simp
    omega
  · rw [Bool.beq_comm]
    split
    · contradiction
    · simp
      have h : (xClientId == yClientId) = false := by
        generalize hEq : (xClientId == yClientId) = eqb at *
        cases eqb <;> simp at *
      rw [beq_eq_false_iff_ne] at h
      omega

namespace YjsLtV2'

theorem first_lt_last {S : ItemSetV2 A} :
    YjsLtV2' S .first .last := by
  exact ⟨ 0, YjsLtV2.ltOriginOrder OriginLtV2.lt_first_last ⟩

theorem first_lt_idRef {S : ItemSetV2 A} {id : YjsId} :
    S.IdIn id ->
    YjsLtV2' S .first (.idRef id) := by
  intro hId
  exact ⟨ 0, YjsLtV2.ltOriginOrder (OriginLtV2.lt_first hId) ⟩

theorem idRef_lt_last {S : ItemSetV2 A} {id : YjsId} :
    S.IdIn id ->
    YjsLtV2' S (.idRef id) .last := by
  intro hId
  exact ⟨ 0, YjsLtV2.ltOriginOrder (OriginLtV2.lt_last hId) ⟩

end YjsLtV2'

namespace YjsLeqV2'

theorem first_leq_of_refIn {S : ItemSetV2 A} {x : ItemRef} :
    S.RefIn x ->
    YjsLeqV2' S .first x := by
  intro hRef
  cases x with
  | first =>
      exact YjsLeqV2'.leqSame _
  | last =>
      exact YjsLeqV2'.leqLt YjsLtV2'.first_lt_last
  | idRef id =>
      exact YjsLeqV2'.leqLt (YjsLtV2'.first_lt_idRef hRef)

theorem leq_last_of_refIn {S : ItemSetV2 A} {x : ItemRef} :
    S.RefIn x ->
    YjsLeqV2' S x .last := by
  intro hRef
  cases x with
  | first =>
      exact YjsLeqV2'.leqLt YjsLtV2'.first_lt_last
  | last =>
      exact YjsLeqV2'.leqSame _
  | idRef id =>
      exact YjsLeqV2'.leqLt (YjsLtV2'.idRef_lt_last hRef)

end YjsLeqV2'

namespace YjsItemSetInvariantV2

theorem pairDepth_induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : ItemRef -> ItemRef -> Prop}
    (step : forall x y,
      (forall x' y', inv.pairDepth x' y' < inv.pairDepth x y -> motive x' y') ->
      motive x y) :
    forall x y, motive x y := by
  let P : Nat -> Prop := fun n => forall x y, inv.pairDepth x y = n -> motive x y
  have hP : forall n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y hEq
    apply step x y
    intro x' y' hLt
    have hLt' : inv.pairDepth x' y' < n := by
      simpa [hEq] using hLt
    exact ih (inv.pairDepth x' y') hLt' x' y' rfl
  intro x y
  exact hP (inv.pairDepth x y) x y rfl

theorem tripleDepth_induction {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S)
    {motive : ItemRef -> ItemRef -> ItemRef -> Prop}
    (step : forall x y z,
      (forall x' y' z', inv.tripleDepth x' y' z' < inv.tripleDepth x y z -> motive x' y' z') ->
      motive x y z) :
    forall x y z, motive x y z := by
  let P : Nat -> Prop := fun n => forall x y z, inv.tripleDepth x y z = n -> motive x y z
  have hP : forall n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih x y z hEq
    apply step x y z
    intro x' y' z' hLt
    have hLt' : inv.tripleDepth x' y' z' < n := by
      simpa [hEq] using hLt
    exact ih (inv.tripleDepth x' y' z') hLt' x' y' z' rfl
  intro x y z
  exact hP (inv.tripleDepth x y z) x y z rfl

theorem yjsLeq_or_yjsLt {S : ItemSetV2 A} (inv : YjsItemSetInvariantV2 S) :
    forall x y, S.RefIn x -> S.RefIn y -> YjsLeqV2' S x y ∨ YjsLtV2' S y x := by
  refine inv.pairDepth_induction
    (motive := fun x y => S.RefIn x -> S.RefIn y -> YjsLeqV2' S x y ∨ YjsLtV2' S y x) ?_
  intro x y ih hx hy
  cases x with
  | first =>
      exact Or.inl (YjsLeqV2'.first_leq_of_refIn hy)
  | last =>
      cases y with
      | first =>
          exact Or.inr YjsLtV2'.first_lt_last
      | last =>
          exact Or.inl (YjsLeqV2'.leqSame _)
      | idRef yid =>
          exact Or.inr (YjsLtV2'.idRef_lt_last hy)
  | idRef xid =>
      cases y with
      | first =>
          exact Or.inr (YjsLtV2'.first_lt_idRef hx)
      | last =>
          exact Or.inl (YjsLeqV2'.leq_last_of_refIn hx)
      | idRef yid =>
          rcases itemIn_of_refIn_idRef_local (S := S) hx with ⟨ xItem, hxItem, hxId ⟩
          rcases itemIn_of_refIn_idRef_local (S := S) hy with ⟨ yItem, hyItem, hyId ⟩

          have hXOriginLt :
              inv.refDepth xItem.origin < inv.refDepth (.idRef xid) := by
            simpa [hxId, YjsItemV2.toRef] using
              inv.origin_depth_lt_toRef_depth (item := xItem) hxItem
          have hXRightLt :
              inv.refDepth xItem.rightOrigin < inv.refDepth (.idRef xid) := by
            simpa [hxId, YjsItemV2.toRef] using
              inv.rightOrigin_depth_lt_toRef_depth (item := xItem) hxItem
          have hYOriginLt :
              inv.refDepth yItem.origin < inv.refDepth (.idRef yid) := by
            simpa [hyId, YjsItemV2.toRef] using
              inv.origin_depth_lt_toRef_depth (item := yItem) hyItem
          have hYRightLt :
              inv.refDepth yItem.rightOrigin < inv.refDepth (.idRef yid) := by
            simpa [hyId, YjsItemV2.toRef] using
              inv.rightOrigin_depth_lt_toRef_depth (item := yItem) hyItem

          have hxyo :
              YjsLeqV2' S (.idRef xid) yItem.origin ∨
                YjsLtV2' S yItem.origin (.idRef xid) := by
            apply ih (.idRef xid) yItem.origin
            · exact inv.pairDepth_lt_of_right_lt hYOriginLt
            · exact hx
            · exact inv.origin_refIn hyItem
          cases hxyo with
          | inl hxyoLeq =>
              have hltXY : YjsLtV2' S (.idRef xid) (.idRef yid) := by
                simpa [YjsItemV2.toRef, hyId] using YjsLtV2'.ltOrigin hyItem hxyoLeq
              exact Or.inl (YjsLeqV2'.leqLt hltXY)
          | inr hyoLtX =>
              have hyrx :
                  YjsLeqV2' S yItem.rightOrigin (.idRef xid) ∨
                    YjsLtV2' S (.idRef xid) yItem.rightOrigin := by
                apply ih yItem.rightOrigin (.idRef xid)
                · simpa [YjsItemSetInvariantV2.pairDepth, Nat.add_comm] using
                    (inv.pairDepth_lt_of_right_lt (z := (.idRef xid)) hYRightLt)
                · exact inv.rightOrigin_refIn hyItem
                · exact hx
              cases hyrx with
              | inl hyrxLeq =>
                  have hltYX : YjsLtV2' S (.idRef yid) (.idRef xid) := by
                    simpa [YjsItemV2.toRef, hyId] using YjsLtV2'.ltRightOrigin hyItem hyrxLeq
                  exact Or.inr hltYX
              | inr hxLtYr =>
                  have hyxo :
                      YjsLeqV2' S (.idRef yid) xItem.origin ∨
                        YjsLtV2' S xItem.origin (.idRef yid) := by
                    apply ih (.idRef yid) xItem.origin
                    · simpa [YjsItemSetInvariantV2.pairDepth, Nat.add_comm] using
                        (inv.pairDepth_lt_of_left_lt (z := (.idRef yid)) hXOriginLt)
                    · exact hy
                    · exact inv.origin_refIn hxItem
                  cases hyxo with
                  | inl hyxoLeq =>
                      have hltYX : YjsLtV2' S (.idRef yid) (.idRef xid) := by
                        simpa [YjsItemV2.toRef, hxId] using YjsLtV2'.ltOrigin hxItem hyxoLeq
                      exact Or.inr hltYX
                  | inr hxoLtY =>
                      have hxry :
                          YjsLeqV2' S xItem.rightOrigin (.idRef yid) ∨
                            YjsLtV2' S (.idRef yid) xItem.rightOrigin := by
                        apply ih xItem.rightOrigin (.idRef yid)
                        · exact inv.pairDepth_lt_of_left_lt hXRightLt
                        · exact inv.rightOrigin_refIn hxItem
                        · exact hy
                      cases hxry with
                      | inl hxryLeq =>
                          have hltXY : YjsLtV2' S (.idRef xid) (.idRef yid) := by
                            simpa [YjsItemV2.toRef, hxId] using YjsLtV2'.ltRightOrigin hxItem hxryLeq
                          exact Or.inl (YjsLeqV2'.leqLt hltXY)
                      | inr hyLtXr =>
                          have hxoyo :
                              YjsLeqV2' S xItem.origin yItem.origin ∨
                                YjsLtV2' S yItem.origin xItem.origin := by
                            apply ih xItem.origin yItem.origin
                            · simpa [YjsItemSetInvariantV2.pairDepth] using
                                Nat.add_lt_add hXOriginLt hYOriginLt
                            · exact inv.origin_refIn hxItem
                            · exact inv.origin_refIn hyItem
                          cases hxoyo with
                          | inr hyoLtXo =>
                              have hConflict : ConflictLtV2' S xItem yItem := by
                                apply ConflictLtV2'.ltOriginDiff
                                · exact hxItem
                                · exact hyItem
                                · exact hyoLtXo
                                · simpa [YjsItemV2.toRef, hxId] using hxLtYr
                                · simpa [YjsItemV2.toRef, hyId] using hxoLtY
                                · simpa [YjsItemV2.toRef, hyId] using hyLtXr
                              have hltXY : YjsLtV2' S (.idRef xid) (.idRef yid) := by
                                simpa [YjsItemV2.toRef, hxId, hyId] using YjsLtV2'.ltConflict hConflict
                              exact Or.inl (YjsLeqV2'.leqLt hltXY)
                          | inl hxoyoLeq =>
                              cases yjsLeqV2_imp_eq_or_yjsLtV2 hxoyoLeq with
                              | inl hOriginEq =>
                                  cases YjsId_lt_total (x := xid) (y := yid) with
                                  | inl hIdLt =>
                                      have hConflict : ConflictLtV2' S xItem yItem := by
                                        apply ConflictLtV2'.ltOriginSame
                                        · exact hxItem
                                        · exact hyItem
                                        · exact hOriginEq
                                        · simpa [YjsItemV2.toRef, hxId] using hxLtYr
                                        · simpa [YjsItemV2.toRef, hyId] using hyLtXr
                                        · simpa [hxId, hyId] using hIdLt
                                      have hltXY : YjsLtV2' S (.idRef xid) (.idRef yid) := by
                                        simpa [YjsItemV2.toRef, hxId, hyId] using YjsLtV2'.ltConflict hConflict
                                      exact Or.inl (YjsLeqV2'.leqLt hltXY)
                                  | inr hRest =>
                                      cases hRest with
                                      | inl hIdLt =>
                                          have hConflict : ConflictLtV2' S yItem xItem := by
                                            apply ConflictLtV2'.ltOriginSame
                                            · exact hyItem
                                            · exact hxItem
                                            · exact hOriginEq.symm
                                            · simpa [YjsItemV2.toRef, hyId] using hyLtXr
                                            · simpa [YjsItemV2.toRef, hxId] using hxLtYr
                                            · simpa [hxId, hyId] using hIdLt
                                          have hltYX : YjsLtV2' S (.idRef yid) (.idRef xid) := by
                                            simpa [YjsItemV2.toRef, hxId, hyId] using YjsLtV2'.ltConflict hConflict
                                          exact Or.inr hltYX
                                      | inr hIdEq =>
                                          cases hIdEq
                                          exact Or.inl (YjsLeqV2'.leqSame _)
                              | inr hxoLtYo =>
                                  have hConflict : ConflictLtV2' S yItem xItem := by
                                    apply ConflictLtV2'.ltOriginDiff
                                    · exact hyItem
                                    · exact hxItem
                                    · exact hxoLtYo
                                    · simpa [YjsItemV2.toRef, hyId] using hyLtXr
                                    · simpa [YjsItemV2.toRef, hxId] using hyoLtX
                                    · simpa [YjsItemV2.toRef, hxId] using hxLtYr
                                  have hltYX : YjsLtV2' S (.idRef yid) (.idRef xid) := by
                                    simpa [YjsItemV2.toRef, hxId, hyId] using YjsLtV2'.ltConflict hConflict
                                  exact Or.inr hltYX

end YjsItemSetInvariantV2
