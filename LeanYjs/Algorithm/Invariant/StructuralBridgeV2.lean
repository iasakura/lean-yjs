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

private theorem oldIdSize_lt_of_dependsOnId {arr : List (YjsItem A)} :
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

end OldToV2
