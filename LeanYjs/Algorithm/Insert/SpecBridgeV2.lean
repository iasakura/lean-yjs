import LeanYjs.Algorithm.Insert.Spec
import LeanYjs.Algorithm.Invariant.YjsArrayBridgeV2

variable {A : Type}
variable [DecidableEq A]

structure IsItemValidV2Against (S : ItemSetV2 A) (item : YjsItem A) : Prop where
  origin_lt_rightOrigin : YjsLtV2' S item.toV2.origin item.toV2.rightOrigin
  reachable_YjsLeq' :
    ∀ x : YjsPtr A,
      OriginReachable item x ->
      YjsLeqV2' S x.toRefV2 item.toV2.origin ∨
      YjsLeqV2' S item.toV2.rightOrigin x.toRefV2

omit [DecidableEq A] in private theorem reachable_in_old_items_of_toItem
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    ∀ {x : YjsPtr A}, OriginReachable newItem x -> ArrSet arr.toList x := by
  intro hArr hToItem x hReach
  have hToItem' := (IntegrateInput.toItem_ok_iff input arr newItem hArr.unique).1 hToItem
  obtain ⟨ origin, rightOrigin, id, content, hDef, hOrigin, hRight, hId, hContent ⟩ := hToItem'
  subst newItem
  have hOriginIn : ArrSet arr.toList origin := by
    cases h_originId : input.originId with
    | none =>
        simp [isLeftIdPtr, h_originId] at hOrigin
        subst hOrigin
        simp [ArrSet]
    | some pid =>
        simp [isLeftIdPtr, h_originId] at hOrigin
        obtain ⟨ item, hEq, hFind ⟩ := hOrigin
        subst hEq
        simp [ArrSet, Array.mem_of_find?_eq_some hFind]
  have hRightIn : ArrSet arr.toList rightOrigin := by
    cases h_rightOriginId : input.rightOriginId with
    | none =>
        simp [isRightIdPtr, h_rightOriginId] at hRight
        subst hRight
        simp [ArrSet]
    | some pid =>
        simp [isRightIdPtr, h_rightOriginId] at hRight
        obtain ⟨ item, hEq, hFind ⟩ := hRight
        subst hEq
        simp [ArrSet, Array.mem_of_find?_eq_some hFind]
  cases hReach with
  | reachable_single _ _ hStep =>
      cases hStep with
      | reachable _ _ _ _ =>
          exact hOriginIn
      | reachable_right _ _ _ _ =>
          exact hRightIn
  | reachable_head _ mid _ hStep hTail =>
      have hMidIn : ArrSet arr.toList mid := by
        cases hStep with
        | reachable _ _ _ _ =>
            exact hOriginIn
        | reachable_right _ _ _ _ =>
            exact hRightIn
      exact reachable_in arr.toList mid hArr.closed _ hTail hMidIn

theorem YjsArrInvariant_integrate_itemSetInvariantV2
    (input : IntegrateInput A) (arr newArr : Array (YjsItem A)) :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    newItem.isValid ->
    maximalId newItem arr ->
    integrate input arr = Except.ok newArr ->
    ∃ i ≤ arr.size,
      newArr = arr.insertIdxIfInBounds i newItem ∧
      YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newArr.toList) := by
  intro hArr hToItem hValid hMaxId hIntegrate
  rcases YjsArrInvariant_integrate input arr newArr hArr hToItem hValid hMaxId hIntegrate with
    ⟨ i, hi, hEq, hNewArrInv ⟩
  exact ⟨ i, hi, hEq, hNewArrInv.itemSetInvariantV2 ⟩

theorem YjsArrInvariant_integrateSafe_itemSetInvariantV2
    (input : IntegrateInput A) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    newItem.isValid ->
    integrateSafe input arr = Except.ok newArr ->
    ∃ i ≤ arr.size,
      newArr = arr.insertIdxIfInBounds i newItem ∧
      YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newArr.toList) := by
  intro hArr hToItem hValid hIntegrate
  rcases YjsArrInvariant_integrateSafe input newItem arr newArr hArr hToItem hValid hIntegrate with
    ⟨ i, hi, hEq, hNewArrInv ⟩
  exact ⟨ i, hi, hEq, hNewArrInv.itemSetInvariantV2 ⟩

theorem YjsStateInvariant_insert_itemSetInvariantV2
    (arr newArr : YjsState A) (input : IntegrateInput A) :
    YjsStateInvariant arr ->
    input.toItem arr.items = Except.ok newItem ->
    newItem.isValid ->
    arr.insert input = Except.ok newArr ->
    YjsItemSetInvariantV2 (ItemSetV2.ofOldItems newArr.items.toList) := by
  intro hState hToItem hValid hInsert
  exact (YjsStateInvariant_insert arr newArr input hState hToItem hValid hInsert).itemSetInvariantV2

theorem YjsItem.isValid_toV2AgainstOldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    newItem.isValid ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.toList) newItem := by
  intro hArr hToItem hValid
  rcases newItem with ⟨ origin, rightOrigin, id, content ⟩
  have hOriginIn : ArrSet arr.toList origin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := origin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable origin rightOrigin id content))
  have hRightIn : ArrSet arr.toList rightOrigin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := rightOrigin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable_right origin rightOrigin id content))
  rcases hValid with ⟨ hLtOld, hReachOld ⟩
  refine ⟨ ?_, ?_ ⟩
  · rcases hLtOld with ⟨ h, hLt ⟩
    exact OldToV2.yjsLt_to_v2 (arr := arr.toList) hArr.closed hArr.uniqueIdOld hLt hOriginIn hRightIn
  · intro x hReach
    have hXIn : ArrSet arr.toList x := reachable_in_old_items_of_toItem hArr hToItem hReach
    cases hReachOld x hReach with
    | inl hLeq =>
        rcases hLeq with ⟨ h, hLeq ⟩
        exact Or.inl <|
          OldToV2.yjsLeq_to_v2 (arr := arr.toList) hArr.closed hArr.uniqueIdOld hLeq hXIn hOriginIn
    | inr hLeq =>
        rcases hLeq with ⟨ h, hLeq ⟩
        exact Or.inr <|
          OldToV2.yjsLeq_to_v2 (arr := arr.toList) hArr.closed hArr.uniqueIdOld hLeq hRightIn hXIn
