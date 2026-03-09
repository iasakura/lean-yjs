import LeanYjs.Algorithm.Invariant.BridgeV2

variable {A : Type}
variable [DecidableEq A]

namespace OldToV2

omit [DecidableEq A] in private theorem eq_of_mem_of_pairwise_id_eq {arr : List (YjsItem A)} {x y : YjsItem A} :
    UniqueIdOld arr ->
    x ∈ arr ->
    y ∈ arr ->
    x.id = y.id ->
    x = y := by
  intro hUnique hx hy hId
  induction arr generalizing x y with
  | nil =>
      cases hx
  | cons head tail ih =>
      simp [UniqueIdOld] at hUnique
      rcases hUnique with ⟨ hHead, hTail ⟩
      simp at hx hy
      cases hx with
      | inl hEq =>
          subst hEq
          cases hy with
          | inl hEq =>
              subst hEq
              rfl
          | inr hyTail =>
              exact False.elim <| hHead y hyTail hId
      | inr hxTail =>
          cases hy with
          | inl hEq =>
              subst hEq
              exact False.elim <| hHead x hxTail hId.symm
          | inr hyTail =>
              exact ih hTail hxTail hyTail hId

private def oldIdSize (arr : List (YjsItem A)) : YjsId -> Nat
  | id =>
      match arr with
      | [] => 0
      | item :: items =>
          if item.id = id then
            item.size
          else
            oldIdSize items id

omit [DecidableEq A] in private theorem oldIdSize_eq_of_mem_of_pairwise {arr : List (YjsItem A)} {item : YjsItem A} :
    UniqueIdOld arr ->
    item ∈ arr ->
    oldIdSize arr item.id = item.size := by
  intro hUnique hMem
  induction arr with
  | nil =>
      cases hMem
  | cons head tail ih =>
      simp [UniqueIdOld] at hUnique
      rcases hUnique with ⟨ hHead, hTail ⟩
      simp [oldIdSize]
      simp at hMem
      cases hMem with
      | inl hEq =>
          subst hEq
          simp
      | inr hMemTail =>
          have hNe : head.id ≠ item.id := by
            intro hEq
            exact hHead item hMemTail hEq
          simp [hNe]
          exact ih hTail hMemTail

omit [DecidableEq A] in private theorem oldIdSize_lt_of_dependsOnId {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ∀ {dep current : YjsId},
      (ItemSetV2.ofOldItems arr).DependsOnId dep current ->
      oldIdSize arr dep < oldIdSize arr current := by
  intro hClosed hUnique dep current hDep
  rcases hDep with ⟨ itemV2, hLookup, hOrigin | hRight ⟩
  · rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hLookup with
      ⟨ oldItem, hMem, hEq ⟩
    rcases oldItem with ⟨ o, r, id, c ⟩
    have hEqId : id = itemV2.id := by
      simpa [YjsItem.toV2] using congrArg YjsItemV2.id hEq
    have hCurrentId : id = current := by
      exact hEqId.trans ((ItemSetV2.ofOldItems arr).lookup_sound hLookup)
    have hCurrentSize : oldIdSize arr current = (YjsItem.mk o r id c).size := by
      rw [← hCurrentId]
      exact oldIdSize_eq_of_mem_of_pairwise hUnique hMem
    have hOriginEq : o.toRefV2 = itemV2.origin := by
      simpa [YjsItem.toV2] using congrArg YjsItemV2.origin hEq
    have hOriginOld : o.toRefV2 = .idRef dep := hOriginEq.trans hOrigin
    cases hO : o with
    | first =>
        simp [YjsPtr.toRefV2, hO] at hOriginOld
    | last =>
        simp [YjsPtr.toRefV2, hO] at hOriginOld
    | itemPtr depItem =>
        simp [YjsPtr.toRefV2, hO] at hOriginOld
        have hDepId : depItem.id = dep := hOriginOld
        have hDepMem : depItem ∈ arr := by
          simpa [ArrSet, hO] using hClosed.closedLeft o r id c hMem
        have hDepSize : oldIdSize arr dep = depItem.size := by
          rw [← hDepId]
          exact oldIdSize_eq_of_mem_of_pairwise hUnique hDepMem
        rw [hDepSize, hCurrentSize]
        simp [YjsPtr.size, YjsItem.size, hO]
        omega
  · rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hLookup with
      ⟨ oldItem, hMem, hEq ⟩
    rcases oldItem with ⟨ o, r, id, c ⟩
    have hEqId : id = itemV2.id := by
      simpa [YjsItem.toV2] using congrArg YjsItemV2.id hEq
    have hCurrentId : id = current := by
      exact hEqId.trans ((ItemSetV2.ofOldItems arr).lookup_sound hLookup)
    have hCurrentSize : oldIdSize arr current = (YjsItem.mk o r id c).size := by
      rw [← hCurrentId]
      exact oldIdSize_eq_of_mem_of_pairwise hUnique hMem
    have hRightEq : r.toRefV2 = itemV2.rightOrigin := by
      simpa [YjsItem.toV2] using congrArg YjsItemV2.rightOrigin hEq
    have hRightOld : r.toRefV2 = .idRef dep := hRightEq.trans hRight
    cases hR : r with
    | first =>
        simp [YjsPtr.toRefV2, hR] at hRightOld
    | last =>
        simp [YjsPtr.toRefV2, hR] at hRightOld
    | itemPtr depItem =>
        simp [YjsPtr.toRefV2, hR] at hRightOld
        have hDepId : depItem.id = dep := hRightOld
        have hDepMem : depItem ∈ arr := by
          simpa [ArrSet, hR] using hClosed.closedRight o r id c hMem
        have hDepSize : oldIdSize arr dep = depItem.size := by
          rw [← hDepId]
          exact oldIdSize_eq_of_mem_of_pairwise hUnique hDepMem
        rw [hDepSize, hCurrentSize]
        simp [YjsPtr.size, YjsItem.size, hR]
        omega

theorem ofOldItems_structural {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ItemSetV2.WellFoundedItemSetV2 (ItemSetV2.ofOldItems arr) := by
  intro hClosed hUnique
  refine ⟨ ?_, ?_ ⟩
  · refine ⟨ ?_, ?_ ⟩
    · intro item hItem
      rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hItem with
        ⟨ oldItem, hMem, hEq ⟩
      have hOriginIn : ArrSet arr oldItem.origin := by
        rcases oldItem with ⟨ o, r, id, c ⟩
        exact hClosed.closedLeft o r id c hMem
      have hRef : (ItemSetV2.ofOldItems arr).RefIn oldItem.origin.toRefV2 := by
        exact arrSet_refIn_toRefV2 (arr := arr) hUnique hOriginIn
      have hOriginEq : oldItem.origin.toRefV2 = item.origin := by
        simpa [YjsItem.toV2] using congrArg YjsItemV2.origin hEq
      simpa [hOriginEq] using hRef
    · intro item hItem
      rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hItem with
        ⟨ oldItem, hMem, hEq ⟩
      have hRightIn : ArrSet arr oldItem.rightOrigin := by
        rcases oldItem with ⟨ o, r, id, c ⟩
        exact hClosed.closedRight o r id c hMem
      have hRef : (ItemSetV2.ofOldItems arr).RefIn oldItem.rightOrigin.toRefV2 := by
        exact arrSet_refIn_toRefV2 (arr := arr) hUnique hRightIn
      have hRightEq : oldItem.rightOrigin.toRefV2 = item.rightOrigin := by
        simpa [YjsItem.toV2] using congrArg YjsItemV2.rightOrigin hEq
      simpa [hRightEq] using hRef
  · refine Subrelation.wf ?_ ((measure (oldIdSize arr)).wf)
    intro dep current hDep
    exact oldIdSize_lt_of_dependsOnId (arr := arr) hClosed hUnique hDep

theorem origin_lt_rightOrigin_field_to_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ItemSetInvariant (ArrSet arr) ->
    ∀ {item : YjsItemV2 A},
      (ItemSetV2.ofOldItems arr).ItemIn item ->
      Exists fun h => YjsLtV2 (ItemSetV2.ofOldItems arr) h item.origin item.rightOrigin := by
  intro hClosed hUnique hInv item hItem
  rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hItem with
    ⟨ oldItem, hMem, hEq ⟩
  simpa [hEq] using origin_lt_rightOrigin_to_v2 (arr := arr) hClosed hUnique hInv hMem

omit [DecidableEq A] in theorem ptr_eq_of_toRefV2_eq {arr : List (YjsItem A)} :
    UniqueIdOld arr ->
    ∀ {p q : YjsPtr A},
      ArrSet arr p ->
      ArrSet arr q ->
      p.toRefV2 = q.toRefV2 ->
      p = q := by
  intro hUnique p q hp hq hEq
  cases p <;> cases q <;> simp [YjsPtr.toRefV2] at hEq ⊢
  case itemPtr.itemPtr item1 item2 =>
      have hItemEq : item1 = item2 := by
        apply eq_of_mem_of_pairwise_id_eq (arr := arr) hUnique <;> assumption
      simp [hItemEq]

omit [DecidableEq A] in theorem originReachableStep_from_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ∀ {x y : ItemRef},
      OriginReachableStepV2 (ItemSetV2.ofOldItems arr) x y ->
      ∃ x' y' : YjsPtr A,
        ArrSet arr x' ∧
        ArrSet arr y' ∧
        x'.toRefV2 = x ∧
        y'.toRefV2 = y ∧
        OriginReachableStep x' y' := by
  intro hClosed hUnique x y hStep
  cases hStep with
  | left hItem =>
      rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hItem with
        ⟨ oldItem, hMem, hEq ⟩
      refine ⟨ oldItem, oldItem.origin, hMem, ?_, ?_, ?_, ?_ ⟩
      · rcases oldItem with ⟨ o, r, id, c ⟩
        exact hClosed.closedLeft o r id c hMem
      · simpa [YjsItem.toV2] using congrArg (fun i => i.toRef) hEq
      · simpa [YjsItem.toV2] using congrArg YjsItemV2.origin hEq
      · rcases oldItem with ⟨ o, r, id, c ⟩
        exact OriginReachableStep.reachable o r id c
  | right hItem =>
      rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hItem with
        ⟨ oldItem, hMem, hEq ⟩
      refine ⟨ oldItem, oldItem.rightOrigin, hMem, ?_, ?_, ?_, ?_ ⟩
      · rcases oldItem with ⟨ o, r, id, c ⟩
        exact hClosed.closedRight o r id c hMem
      · simpa [YjsItem.toV2] using congrArg (fun i => i.toRef) hEq
      · simpa [YjsItem.toV2] using congrArg YjsItemV2.rightOrigin hEq
      · rcases oldItem with ⟨ o, r, id, c ⟩
        exact OriginReachableStep.reachable_right o r id c

omit [DecidableEq A] in theorem originReachable_from_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ∀ {x y : ItemRef},
      OriginReachableV2 (ItemSetV2.ofOldItems arr) x y ->
      ∃ x' y' : YjsPtr A,
        ArrSet arr x' ∧
        ArrSet arr y' ∧
        x'.toRefV2 = x ∧
        y'.toRefV2 = y ∧
        OriginReachable x' y' := by
  intro hClosed hUnique x y hReach
  induction hReach with
  | single hStep =>
      rcases originReachableStep_from_v2 (arr := arr) hClosed hUnique hStep with
        ⟨ x', y', hx, hy, hxEq, hyEq, hStepOld ⟩
      exact ⟨ x', y', hx, hy, hxEq, hyEq, .reachable_single _ _ hStepOld ⟩
  | tail hStep hTail ih =>
      rcases originReachableStep_from_v2 (arr := arr) hClosed hUnique hStep with
        ⟨ x1, y1, hx1, hy1, hxEq, hyEq, hStepOld ⟩
      rcases ih with ⟨ x2, z2, hx2, hz2, hxEq2, hzEq, hTailOld ⟩
      have hMidEq : y1 = x2 := by
        apply ptr_eq_of_toRefV2_eq (arr := arr) hUnique hy1 hx2
        exact hyEq.trans hxEq2.symm
      subst x2
      exact ⟨ x1, z2, hx1, hz2, hxEq, hzEq, .reachable_head _ _ _ hStepOld hTailOld ⟩

theorem ofOldItems_invariant_v2 {arr : List (YjsItem A)} :
    ArrSetClosed arr ->
    UniqueIdOld arr ->
    ItemSetInvariant (ArrSet arr) ->
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems arr) := by
  intro hClosed hUnique hInv
  refine ⟨ ofOldItems_structural (arr := arr) hClosed hUnique, ?_, ?_ ⟩
  · exact origin_lt_rightOrigin_field_to_v2 (arr := arr) hClosed hUnique hInv
  · intro item x hItem hReach
    rcases ItemSetV2.exists_oldItem_of_lookup_eq_some (items := arr) hItem with
      ⟨ oldItem, hMem, hEq ⟩
    rcases originReachable_from_v2 (arr := arr) hClosed hUnique hReach with
      ⟨ xOld, yOld, hxOld, hyOld, hxEq, hyEq, hReachOld ⟩
    have hStartRefEq : xOld.toRefV2 = ((oldItem : YjsPtr A).toRefV2) := by
      calc
        xOld.toRefV2 = item.toRef := hxEq
        _ = oldItem.toV2.toRef := by
          simpa using (congrArg (fun i => i.toRef) hEq).symm
        _ = ((oldItem : YjsPtr A).toRefV2) := by
          simp [YjsItem.toV2, YjsPtr.toRefV2]
    have hStartEq : xOld = oldItem := by
      exact ptr_eq_of_toRefV2_eq (arr := arr) hUnique hxOld hMem hStartRefEq
    subst xOld
    simpa [hEq, hyEq] using
      origin_nearest_reachable_to_v2 (arr := arr) hClosed hUnique hInv hMem hReachOld

end OldToV2
