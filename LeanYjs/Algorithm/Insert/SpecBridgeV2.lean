import LeanYjs.Algorithm.Insert.Spec
import LeanYjs.Algorithm.Insert.SpecPortV2
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

omit [DecidableEq A] in private theorem toItem_id_eq_local
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    newItem.id = input.id := by
  intro hArr hToItem
  rw [IntegrateInput.toItem_ok_iff _ _ _ hArr.unique] at hToItem
  obtain ⟨ origin, rightOrigin, id, content, hDef, _, _, hId, _ ⟩ := hToItem
  subst newItem
  simpa using hId

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

theorem toItem_origin_refIn_oldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.toV2.origin := by
  intro hArr hToItem
  rcases newItem with ⟨ origin, rightOrigin, id, content ⟩
  have hOriginIn : ArrSet arr.toList origin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := origin)
      (OriginReachable.reachable_single _ _ <|
        OriginReachableStep.reachable _ _ _ _)
  simpa [YjsItem.toV2] using
    OldToV2.arrSet_refIn_toRefV2 (arr := arr.toList) hArr.uniqueIdOld hOriginIn

theorem toItem_rightOrigin_refIn_oldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.toV2.rightOrigin := by
  intro hArr hToItem
  rcases newItem with ⟨ origin, rightOrigin, id, content ⟩
  have hRightIn : ArrSet arr.toList rightOrigin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := rightOrigin)
      (OriginReachable.reachable_single _ _ <|
        OriginReachableStep.reachable_right _ _ _ _)
  simpa [YjsItem.toV2] using
    OldToV2.arrSet_refIn_toRefV2 (arr := arr.toList) hArr.uniqueIdOld hRightIn

theorem activeSetV2_structural_of_toItem_maximalId
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    maximalId newItem arr ->
    ItemSetV2.WellFoundedItemSetV2 (activeSetV2 arr newItem.toV2) := by
  intro hArr hToItem hMax
  have hToItemV2 : input.toItemV2 arr = Except.ok newItem.toV2 := by
    exact IntegrateInput.toItem_toItemV2 hToItem
  have hSafe : isClockSafe input.id arr = true := by
    rw [← isClockSafe_maximalId hArr.unique hToItem]
    exact hMax
  exact activeSetV2_structural_of_toItemV2_isClockSafe hArr hSafe hToItemV2

theorem originReachable_to_fromV2AgainstOldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} {x : YjsPtr A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    OriginReachable newItem x ->
    OriginReachableFromV2 (ItemSetV2.ofOldItems arr.toList) newItem.toV2 x.toRefV2 := by
  intro hArr hToItem hReach
  rcases newItem with ⟨ origin, rightOrigin, id, content ⟩
  have hOriginIn : ArrSet arr.toList origin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := origin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable origin rightOrigin id content))
  have hRightIn : ArrSet arr.toList rightOrigin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := rightOrigin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable_right origin rightOrigin id content))
  exact OldToV2.originReachableFrom_to_v2 (arr := arr.toList)
    hArr.closed hArr.uniqueIdOld hOriginIn hRightIn hReach

theorem not_originReachable_of_not_fromV2AgainstOldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} {x : YjsPtr A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    ¬ OriginReachableFromV2 (ItemSetV2.ofOldItems arr.toList) newItem.toV2 x.toRefV2 ->
    ¬ OriginReachable newItem x := by
  intro hArr hToItem hNotV2 hReach
  exact hNotV2 <|
    originReachable_to_fromV2AgainstOldItems hArr hToItem hReach

namespace IsItemValidV2Against

theorem reachable_YjsLeq_fromV2AgainstOldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A}
    {x : ItemRef} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.toList) newItem ->
    OriginReachableFromV2 (ItemSetV2.ofOldItems arr.toList) newItem.toV2 x ->
    YjsLeqV2' (ItemSetV2.ofOldItems arr.toList) x newItem.toV2.origin ∨
    YjsLeqV2' (ItemSetV2.ofOldItems arr.toList) newItem.toV2.rightOrigin x := by
  intro hArr hToItem hValid hReach
  rcases newItem with ⟨ origin, rightOrigin, id, content ⟩
  have hOriginIn : ArrSet arr.toList origin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := origin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable origin rightOrigin id content))
  have hRightIn : ArrSet arr.toList rightOrigin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := rightOrigin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable_right origin rightOrigin id content))
  cases hReach with
  | origin =>
      exact Or.inl (YjsLeqV2'.leqSame _)
  | rightOrigin =>
      exact Or.inr (YjsLeqV2'.leqSame _)
  | tail_origin hReachV2 =>
      rcases OldToV2.originReachable_from_v2 (arr := arr.toList) hArr.closed hArr.uniqueIdOld hReachV2 with
        ⟨ xOld, yOld, hxOld, hyOld, hxEq, hyEq, hReachOld ⟩
      have hStartEq : xOld = origin := by
        apply OldToV2.ptr_eq_of_toRefV2_eq (arr := arr.toList) hArr.uniqueIdOld hxOld hOriginIn
        simpa [YjsItem.toV2] using hxEq
      subst xOld
      have hReachItem : OriginReachable (YjsItem.mk origin rightOrigin id content) yOld := by
        exact .reachable_head _ _ _
          (OriginReachableStep.reachable origin rightOrigin id content) hReachOld
      simpa [YjsItem.toV2, hyEq] using hValid.reachable_YjsLeq' yOld hReachItem
  | tail_rightOrigin hReachV2 =>
      rcases OldToV2.originReachable_from_v2 (arr := arr.toList) hArr.closed hArr.uniqueIdOld hReachV2 with
        ⟨ xOld, yOld, hxOld, hyOld, hxEq, hyEq, hReachOld ⟩
      have hStartEq : xOld = rightOrigin := by
        apply OldToV2.ptr_eq_of_toRefV2_eq (arr := arr.toList) hArr.uniqueIdOld hxOld hRightIn
        simpa [YjsItem.toV2] using hxEq
      subst xOld
      have hReachItem : OriginReachable (YjsItem.mk origin rightOrigin id content) yOld := by
        exact .reachable_head _ _ _
          (OriginReachableStep.reachable_right origin rightOrigin id content) hReachOld
      simpa [YjsItem.toV2, hyEq] using hValid.reachable_YjsLeq' yOld hReachItem

end IsItemValidV2Against

theorem activeSetV2_origin_lt_rightOrigin_of_valid
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    maximalId newItem arr ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.toList) newItem ->
    YjsLtV2' (activeSetV2 arr newItem.toV2) newItem.toV2.origin newItem.toV2.rightOrigin := by
  intro hArr hToItem hMax hValid
  have hSafe : isClockSafe input.id arr = true := by
    rw [← isClockSafe_maximalId hArr.unique hToItem]
    exact hMax
  have hFresh : (ItemSetV2.ofOldItems arr.toList).lookup newItem.id = none := by
    have hId : newItem.id = input.id := toItem_id_eq_local hArr hToItem
    simpa [hId] using ofOldItems_lookup_none_of_isClockSafe hSafe
  exact activeSetV2_yjsLt_of_old hFresh hValid.origin_lt_rightOrigin

theorem activeSetV2_origin_nearest_reachable_of_valid
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A}
    {x : ItemRef} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    maximalId newItem arr ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.toList) newItem ->
    OriginReachableV2 (activeSetV2 arr newItem.toV2) newItem.toV2.toRef x ->
    YjsLeqV2' (activeSetV2 arr newItem.toV2) x newItem.toV2.origin ∨
    YjsLeqV2' (activeSetV2 arr newItem.toV2) newItem.toV2.rightOrigin x := by
  intro hArr hToItem hMax hValid hReach
  have hSafe : isClockSafe input.id arr = true := by
    rw [← isClockSafe_maximalId hArr.unique hToItem]
    exact hMax
  have hFresh : (ItemSetV2.ofOldItems arr.toList).lookup newItem.id = none := by
    have hId : newItem.id = input.id := toItem_id_eq_local hArr hToItem
    simpa [hId] using ofOldItems_lookup_none_of_isClockSafe hSafe
  have hOriginRef :
      (ItemSetV2.ofOldItems arr.toList).RefIn newItem.toV2.origin := by
    exact toItem_origin_refIn_oldItems hArr hToItem
  have hRightRef :
      (ItemSetV2.ofOldItems arr.toList).RefIn newItem.toV2.rightOrigin := by
    exact toItem_rightOrigin_refIn_oldItems hArr hToItem
  have hReachOld :
      OriginReachableFromV2 (ItemSetV2.ofOldItems arr.toList) newItem.toV2 x := by
    exact originReachableFromV2_of_withItem
      (S := ItemSetV2.ofOldItems arr.toList) hArr.itemSetInvariantV2.closed
      hFresh hOriginRef hRightRef hReach
  have hNearOld :=
    IsItemValidV2Against.reachable_YjsLeq_fromV2AgainstOldItems hArr hToItem hValid hReachOld
  cases hNearOld with
  | inl hLeq =>
      exact Or.inl (activeSetV2_yjsLeq_of_old hFresh hLeq)
  | inr hLeq =>
      exact Or.inr (activeSetV2_yjsLeq_of_old hFresh hLeq)

theorem YjsItem.isValid_of_v2AgainstOldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.toList) newItem ->
    newItem.isValid := by
  intro hArr hToItem hValidV2
  rcases newItem with ⟨ origin, rightOrigin, id, content ⟩
  have hOriginIn : ArrSet arr.toList origin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := origin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable origin rightOrigin id content))
  have hRightIn : ArrSet arr.toList rightOrigin := by
    exact reachable_in_old_items_of_toItem hArr hToItem
      (x := rightOrigin)
      (OriginReachable.reachable_single _ _ (OriginReachableStep.reachable_right origin rightOrigin id content))
  refine ⟨ ?_, ?_ ⟩
  · exact OldToV2.yjsLt_from_v2 (arr := arr.toList)
      hArr.closed hArr.uniqueIdOld hArr.item_set_inv hOriginIn hRightIn
      hValidV2.origin_lt_rightOrigin
  · intro x hReach
    have hXIn : ArrSet arr.toList x := reachable_in_old_items_of_toItem hArr hToItem hReach
    cases hValidV2.reachable_YjsLeq' x hReach with
    | inl hLeq =>
        exact Or.inl <|
          OldToV2.yjsLeq_from_v2 (arr := arr.toList)
            hArr.closed hArr.uniqueIdOld hArr.item_set_inv hXIn hOriginIn hLeq
    | inr hLeq =>
        exact Or.inr <|
          OldToV2.yjsLeq_from_v2 (arr := arr.toList)
            hArr.closed hArr.uniqueIdOld hArr.item_set_inv hRightIn hXIn hLeq

theorem YjsItem.isValid_iff_v2AgainstOldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItem A} :
    YjsArrInvariant arr.toList ->
    input.toItem arr = Except.ok newItem ->
    (newItem.isValid ↔ IsItemValidV2Against (ItemSetV2.ofOldItems arr.toList) newItem) := by
  intro hArr hToItem
  constructor
  · exact YjsItem.isValid_toV2AgainstOldItems hArr hToItem
  · exact YjsItem.isValid_of_v2AgainstOldItems hArr hToItem
