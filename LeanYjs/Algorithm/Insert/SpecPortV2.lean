import LeanYjs.Algorithm.Insert.BasicV2
import LeanYjs.Algorithm.Invariant.YjsArrayBridgeV2

variable {A : Type} [DecidableEq A]

def activeSetV2 (arr : Array (YjsItem A)) (newItem : YjsItemV2 A) : ItemSetV2 A :=
  (ItemSetV2.ofOldItems arr.toList).withItem newItem

def offsetToIndexV2 (leftIdx : Int) (rightIdx : Int) (offset : Option Nat) (isBreak : Bool) : Nat :=
  let back := if isBreak then 1 else 0
  match offset with
  | none => rightIdx.toNat - back
  | some o => (leftIdx + o).toNat - back

def isBreakV2 (state : ForInStep (MProd Int Bool)) : Bool :=
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

def isDoneV2 (state : ForInStep (MProd Int Bool)) (x : Option Nat) : Bool :=
  (match x with
  | none => true
  | some _ => false) ||
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

abbrev extGetElemExceptV2 (arr : Array (YjsItem A)) (idx : Int) : Except IntegrateError ItemRef :=
  getRefExcept arr idx

def loopInvV2 (arr : Array (YjsItem A)) (newItem : YjsItemV2 A)
    (leftIdx rightIdx : Int) (x : Option Nat) (state : ForInStep (MProd Int Bool)) : Prop :=
  let current := offsetToIndexV2 leftIdx rightIdx x (isBreakV2 state)
  let S := activeSetV2 arr newItem
  let ⟨ dest, scanning ⟩ := state.value
  let done := isDoneV2 state x
  (match x with
    | none => True
    | some x => 0 < x ∧ x < (rightIdx - leftIdx).toNat) ∧
  (dest ≤ current) ∧
  (!scanning → !done -> dest = current) ∧
  let dest := dest.toNat
  (∀ i : Nat, i < dest -> (h_i_lt : i < arr.size) -> YjsLtV2' S arr[i].toV2.toRef newItem.toRef) ∧
  (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
    ∃ (i_lt_size : i < arr.size) (h_dest_lt : dest < arr.size),
      (arr[i].toV2.origin = newItem.origin ∧ newItem.id < arr[i].id ∨
        YjsLeqV2' S arr[dest].toV2.toRef arr[i].toV2.origin)) ∧
  (scanning -> ∃ h_dest_lt : dest < arr.size, arr[dest].toV2.origin = newItem.origin) ∧
  (done -> ∀ item : ItemRef, extGetElemExceptV2 arr current = Except.ok item -> YjsLtV2' S newItem.toRef item)

omit [DecidableEq A] in theorem offsetToIndexV2_range'_getElem {leftIdx rightIdx : Int} {offset : Nat} :
    -1 ≤ leftIdx ->
    0 ≤ rightIdx ->
    offset ≤ rightIdx - leftIdx - 1 ->
    offsetToIndexV2 leftIdx rightIdx (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[offset]?
        (isBreakV2 state) =
      (leftIdx + offset + 1).toNat - (if isBreakV2 state then 1 else 0) := by
  intro hLeftIdx hRightIdx hLe
  generalize hGet : (List.range' 1 ((rightIdx - leftIdx).toNat - 1))[offset]? = i at *
  cases i with
  | none =>
      simp [offsetToIndexV2]
      rw [List.getElem?_eq_none_iff] at hGet
      rw [List.length_range'] at hGet
      omega
  | some o =>
      simp [offsetToIndexV2]
      rw [List.getElem?_eq_some_iff] at hGet
      obtain ⟨ hLength, hEq ⟩ := hGet
      rw [List.getElem_range'] at hEq
      rw [List.length_range'] at hLength
      omega

omit [DecidableEq A] in theorem loopInvV2_offset_bounds
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A}
    {leftIdx rightIdx : Int} {x : Option Nat} {state : ForInStep (MProd Int Bool)} :
    loopInvV2 arr newItem leftIdx rightIdx x state ->
    match x with
    | none => True
    | some x => 0 < x ∧ x < (rightIdx - leftIdx).toNat := by
  intro hInv
  unfold loopInvV2 at hInv
  simpa using hInv.1

omit [DecidableEq A] in theorem loopInvV2_dest_le_current
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A}
    {leftIdx rightIdx : Int} {x : Option Nat} {state : ForInStep (MProd Int Bool)} :
    loopInvV2 arr newItem leftIdx rightIdx x state ->
    state.value.fst ≤ offsetToIndexV2 leftIdx rightIdx x (isBreakV2 state) := by
  intro hInv
  unfold loopInvV2 at hInv
  exact hInv.2.1

theorem loopInvV2_dest_eq_current_of_not_scanning
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A}
    {leftIdx rightIdx : Int} {x : Option Nat} {state : ForInStep (MProd Int Bool)} :
    loopInvV2 arr newItem leftIdx rightIdx x state ->
    state.value.snd = false ->
    isDoneV2 state x = false ->
    state.value.fst = offsetToIndexV2 leftIdx rightIdx x (isBreakV2 state) := by
  intro hInv hScanning hDone
  unfold loopInvV2 at hInv
  exact hInv.2.2.1 (by simpa [hScanning]) (by simpa [hDone])

theorem loopInvV2_lt_prefix
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A}
    {leftIdx rightIdx : Int} {x : Option Nat} {state : ForInStep (MProd Int Bool)} :
    loopInvV2 arr newItem leftIdx rightIdx x state ->
    ∀ i : Nat, i < state.value.fst.toNat -> (h_i_lt : i < arr.size) ->
      YjsLtV2' (activeSetV2 arr newItem) arr[i].toV2.toRef newItem.toRef := by
  intro hInv i hLt hILt
  unfold loopInvV2 at hInv
  exact hInv.2.2.2.1 i hLt hILt

theorem loopInvV2_scanning_origin
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A}
    {leftIdx rightIdx : Int} {x : Option Nat} {state : ForInStep (MProd Int Bool)} :
    loopInvV2 arr newItem leftIdx rightIdx x state ->
    state.value.snd = true ->
    ∃ h_dest_lt : state.value.fst.toNat < arr.size,
      arr[state.value.fst.toNat].toV2.origin = newItem.origin := by
  intro hInv hScanning
  unfold loopInvV2 at hInv
  exact hInv.2.2.2.2.2.1 (by simpa [hScanning])

theorem loopInvV2_done_lt
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A}
    {leftIdx rightIdx : Int} {x : Option Nat} {state : ForInStep (MProd Int Bool)}
    {item : ItemRef} :
    loopInvV2 arr newItem leftIdx rightIdx x state ->
    isDoneV2 state x = true ->
    extGetElemExceptV2 arr (offsetToIndexV2 leftIdx rightIdx x (isBreakV2 state)) = Except.ok item ->
    YjsLtV2' (activeSetV2 arr newItem) newItem.toRef item := by
  intro hInv hDone hItem
  unfold loopInvV2 at hInv
  exact hInv.2.2.2.2.2.2 (by simpa [hDone]) item hItem

omit [DecidableEq A] in theorem activeSetV2_itemIn_newItem
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    (activeSetV2 arr newItem).ItemIn newItem := by
  exact ItemSetV2.itemIn_withItem (S := ItemSetV2.ofOldItems arr.toList) (item := newItem)

omit [DecidableEq A] in theorem activeSetV2_refIn_newItem
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    (activeSetV2 arr newItem).RefIn newItem.toRef := by
  exact ItemSetV2.refIn_of_itemIn activeSetV2_itemIn_newItem

omit [DecidableEq A] in theorem activeSetV2_refIn_of_oldRefIn
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} {ref : ItemRef} :
    (ItemSetV2.ofOldItems arr.toList).RefIn ref ->
    (activeSetV2 arr newItem).RefIn ref := by
  intro hRef
  exact ItemSetV2.refIn_withItem_of_refIn (S := ItemSetV2.ofOldItems arr.toList)
    (item := newItem) hRef

omit [DecidableEq A] in private theorem find_item_id_eq_v2
    {arr : Array (YjsItem A)} {targetId : YjsId} {item : YjsItem A} :
    arr.find? (fun cand => cand.id = targetId) = some item ->
    item.id = targetId := by
  intro hFind
  rw [Array.find?_eq_some_iff_getElem] at hFind
  simp at hFind
  obtain ⟨ hId, _, _, _, _ ⟩ := hFind
  exact hId

omit [DecidableEq A] in theorem toItemV2_origin_refIn_oldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    input.toItemV2 arr = Except.ok newItem ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.origin := by
  intro hArr hToItem
  cases hOriginId : input.originId with
  | none =>
      cases hRightOriginId : input.rightOriginId with
      | none =>
          simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
            hOriginId, hRightOriginId] at hToItem ⊢
          cases hToItem
          simp
      | some rightOriginId =>
          cases hFindRight : arr.find? (fun item => item.id = rightOriginId) with
          | none =>
              have : False := by
                simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                  hOriginId, hRightOriginId, hFindRight] using hToItem
              exact False.elim this
          | some rightItem =>
              simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                hOriginId, hRightOriginId, hFindRight] at hToItem ⊢
              cases hToItem
              simp
  | some originId =>
      cases hFindOrigin : arr.find? (fun item => item.id = originId) with
      | none =>
          have : False := by
            simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
              hOriginId, hFindOrigin] using hToItem
          exact False.elim this
      | some originItem =>
          have hOriginEq : originItem.id = originId := find_item_id_eq_v2 hFindOrigin
          have hOriginMem : originItem ∈ arr.toList := by
            simpa using Array.mem_of_find?_eq_some hFindOrigin
          have hOriginRef : (ItemSetV2.ofOldItems arr.toList).RefIn originItem.toV2.toRef := by
            exact ItemSetV2.refIn_toRef_of_mem_of_pairwise
              (items := arr.toList) (item := originItem) hArr.unique hOriginMem
          cases hRightOriginId : input.rightOriginId with
          | none =>
              simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                hOriginId, hRightOriginId, hFindOrigin] at hToItem ⊢
              cases hToItem
              simpa [YjsItem.toV2, hOriginEq] using hOriginRef
          | some rightOriginId =>
              cases hFindRight : arr.find? (fun item => item.id = rightOriginId) with
              | none =>
                  have : False := by
                    simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                      hOriginId, hRightOriginId, hFindOrigin, hFindRight] using hToItem
                  exact False.elim this
              | some rightItem =>
                  simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                    hOriginId, hRightOriginId, hFindOrigin, hFindRight] at hToItem ⊢
                  cases hToItem
                  simpa [YjsItem.toV2, hOriginEq] using hOriginRef

omit [DecidableEq A] in theorem toItemV2_rightOrigin_refIn_oldItems
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    input.toItemV2 arr = Except.ok newItem ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.rightOrigin := by
  intro hArr hToItem
  cases hRightOriginId : input.rightOriginId with
  | none =>
      cases hOriginId : input.originId with
      | none =>
          simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
            hOriginId, hRightOriginId] at hToItem ⊢
          cases hToItem
          simp
      | some originId =>
          cases hFindOrigin : arr.find? (fun item => item.id = originId) with
          | none =>
              have : False := by
                simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                  hOriginId, hRightOriginId, hFindOrigin] using hToItem
              exact False.elim this
          | some originItem =>
              simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                hOriginId, hRightOriginId, hFindOrigin] at hToItem ⊢
              cases hToItem
              simp
  | some rightOriginId =>
      cases hOriginId : input.originId with
      | none =>
          cases hFindRight : arr.find? (fun item => item.id = rightOriginId) with
          | none =>
              have : False := by
                simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                  hOriginId, hRightOriginId, hFindRight] using hToItem
              exact False.elim this
          | some rightItem =>
              have hRightEq : rightItem.id = rightOriginId := find_item_id_eq_v2 hFindRight
              have hRightMem : rightItem ∈ arr.toList := by
                simpa using Array.mem_of_find?_eq_some hFindRight
              have hRightRef : (ItemSetV2.ofOldItems arr.toList).RefIn rightItem.toV2.toRef := by
                exact ItemSetV2.refIn_toRef_of_mem_of_pairwise
                  (items := arr.toList) (item := rightItem) hArr.unique hRightMem
              simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                hOriginId, hRightOriginId, hFindRight] at hToItem ⊢
              cases hToItem
              simpa [YjsItem.toV2, hRightEq] using hRightRef
      | some originId =>
          cases hFindOrigin : arr.find? (fun item => item.id = originId) with
          | none =>
              have : False := by
                simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                  hOriginId, hFindOrigin] using hToItem
              exact False.elim this
          | some originItem =>
              cases hFindRight : arr.find? (fun item => item.id = rightOriginId) with
              | none =>
                  have : False := by
                    simpa [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                      hOriginId, hRightOriginId, hFindOrigin, hFindRight] using hToItem
                  exact False.elim this
              | some rightItem =>
                  have hRightEq : rightItem.id = rightOriginId := find_item_id_eq_v2 hFindRight
                  have hRightMem : rightItem ∈ arr.toList := by
                    simpa using Array.mem_of_find?_eq_some hFindRight
                  have hRightRef : (ItemSetV2.ofOldItems arr.toList).RefIn rightItem.toV2.toRef := by
                    exact ItemSetV2.refIn_toRef_of_mem_of_pairwise
                      (items := arr.toList) (item := rightItem) hArr.unique hRightMem
                  simp [IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                    hOriginId, hRightOriginId, hFindOrigin, hFindRight] at hToItem ⊢
                  cases hToItem
                  simpa [YjsItem.toV2, hRightEq] using hRightRef

theorem activeSetV2_closed
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.origin ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.rightOrigin ->
    ItemSetV2.IsClosedItemSetV2 (activeSetV2 arr newItem) := by
  intro hArr hOrigin hRight
  exact ItemSetV2.isClosed_withItem hArr.itemSetInvariantV2.closed hOrigin hRight

theorem activeSetV2_structural
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    (ItemSetV2.ofOldItems arr.toList).lookup newItem.id = none ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.origin ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.rightOrigin ->
    ItemSetV2.WellFoundedItemSetV2 (activeSetV2 arr newItem) := by
  intro hArr hFresh hOrigin hRight
  simpa [activeSetV2] using
    ItemSetV2.wellFounded_withItem hArr.itemSetInvariantV2.structural hFresh hOrigin hRight

theorem activeSetV2_structural_of_toItemV2_isClockSafe
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    isClockSafe input.id arr = true ->
    input.toItemV2 arr = Except.ok newItem ->
    ItemSetV2.WellFoundedItemSetV2 (activeSetV2 arr newItem) := by
  intro hArr hSafe hToItem
  apply activeSetV2_structural hArr
  · have hFresh : (ItemSetV2.ofOldItems arr.toList).lookup input.id = none := by
      exact ofOldItems_lookup_none_of_isClockSafe hSafe
    have hId : newItem.id = input.id := IntegrateInput.toItemV2_id_eq hToItem
    simpa [hId] using hFresh
  · exact toItemV2_origin_refIn_oldItems hArr hToItem
  · exact toItemV2_rightOrigin_refIn_oldItems hArr hToItem

theorem activeSetV2_closed_of_toItemV2
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    input.toItemV2 arr = Except.ok newItem ->
    ItemSetV2.IsClosedItemSetV2 (activeSetV2 arr newItem) := by
  intro hArr hToItem
  apply activeSetV2_closed hArr
  · exact toItemV2_origin_refIn_oldItems hArr hToItem
  · exact toItemV2_rightOrigin_refIn_oldItems hArr hToItem

omit [DecidableEq A] in theorem getRefExcept_refIn_oldItems
    {arr : Array (YjsItem A)} {idx : Int} {ref : ItemRef} :
    YjsArrInvariant arr.toList ->
    (-1 : Int) ≤ idx ->
    idx ≤ arr.size ->
    getRefExcept arr idx = Except.ok ref ->
    (ItemSetV2.ofOldItems arr.toList).RefIn ref := by
  intro hArr hLow hHigh hGet
  by_cases hFirst : idx = -1
  · simp [getRefExcept, hFirst] at hGet ⊢
    cases hGet
    simp
  · by_cases hLast : idx = arr.size
    · simp [getRefExcept, hFirst, hLast] at hGet ⊢
      cases hGet
      simp
    · unfold getRefExcept at hGet
      simp [hFirst, hLast] at hGet
      cases hItem : arr[idx.toNat]? with
      | none =>
          simp [hItem] at hGet
      | some item =>
          simp [hItem] at hGet
          cases hGet
          have hNonneg : (0 : Int) ≤ idx := by
            omega
          have hLt : idx < arr.size := by
            omega
          have hNatLt : idx.toNat < arr.size := (Int.toNat_lt hNonneg).2 hLt
          have hMem : item ∈ arr.toList := by
            have hMemArr : item ∈ arr := by
              rw [Array.mem_iff_getElem]
              rw [Array.getElem?_eq_some_iff] at hItem
              exact ⟨ idx.toNat, hNatLt, hItem.2 ⟩
            simpa using hMemArr
          simpa [YjsItem.toV2] using
            ItemSetV2.refIn_toRef_of_mem_of_pairwise
              (items := arr.toList) (item := item) hArr.unique hMem

omit [DecidableEq A] in theorem mkItemV2ByIndex_origin_refIn_oldItems
    {leftIdx rightIdx : Int} {input : IntegrateInput A}
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    (-1 : Int) ≤ leftIdx ->
    leftIdx ≤ arr.size ->
    mkItemV2ByIndex leftIdx rightIdx input arr = Except.ok newItem ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.origin := by
  intro hArr hLeftLow hLeftHigh hMk
  unfold mkItemV2ByIndex at hMk
  cases hLeft : getRefExcept arr leftIdx with
  | error err =>
      simp [bind, Except.bind, hLeft] at hMk
  | ok leftRef =>
      cases hRight : getRefExcept arr rightIdx with
      | error err =>
          simp [bind, Except.bind, hLeft, hRight] at hMk
      | ok rightRef =>
          simp [bind, Except.bind, pure, Except.pure, hLeft, hRight] at hMk
          cases hMk
          simpa using getRefExcept_refIn_oldItems hArr hLeftLow hLeftHigh hLeft

omit [DecidableEq A] in theorem mkItemV2ByIndex_rightOrigin_refIn_oldItems
    {leftIdx rightIdx : Int} {input : IntegrateInput A}
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    (-1 : Int) ≤ rightIdx ->
    rightIdx ≤ arr.size ->
    mkItemV2ByIndex leftIdx rightIdx input arr = Except.ok newItem ->
    (ItemSetV2.ofOldItems arr.toList).RefIn newItem.rightOrigin := by
  intro hArr hRightLow hRightHigh hMk
  unfold mkItemV2ByIndex at hMk
  cases hLeft : getRefExcept arr leftIdx with
  | error err =>
      simp [bind, Except.bind, hLeft] at hMk
  | ok leftRef =>
      cases hRight : getRefExcept arr rightIdx with
      | error err =>
          simp [bind, Except.bind, hLeft, hRight] at hMk
      | ok rightRef =>
          simp [bind, Except.bind, pure, Except.pure, hLeft, hRight] at hMk
          cases hMk
          simpa using getRefExcept_refIn_oldItems hArr hRightLow hRightHigh hRight

theorem activeSetV2_closed_of_mkItemV2ByIndex
    {leftIdx rightIdx : Int} {input : IntegrateInput A}
    {arr : Array (YjsItem A)} {newItem : YjsItemV2 A} :
    YjsArrInvariant arr.toList ->
    (-1 : Int) ≤ leftIdx ->
    leftIdx ≤ arr.size ->
    (-1 : Int) ≤ rightIdx ->
    rightIdx ≤ arr.size ->
    mkItemV2ByIndex leftIdx rightIdx input arr = Except.ok newItem ->
    ItemSetV2.IsClosedItemSetV2 (activeSetV2 arr newItem) := by
  intro hArr hLeftLow hLeftHigh hRightLow hRightHigh hMk
  apply activeSetV2_closed hArr
  · exact mkItemV2ByIndex_origin_refIn_oldItems hArr hLeftLow hLeftHigh hMk
  · exact mkItemV2ByIndex_rightOrigin_refIn_oldItems hArr hRightLow hRightHigh hMk
