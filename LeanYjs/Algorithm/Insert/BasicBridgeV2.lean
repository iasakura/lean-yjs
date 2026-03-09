import LeanYjs.Algorithm.Insert.BasicV2
import LeanYjs.Algorithm.Invariant.YjsArray

variable {A : Type} [DecidableEq A]

def scanStepV2 (arr : Array (YjsItem A)) (input : IntegrateInput A)
    (leftIdx rightIdx : Int) (offset : Nat) (state : MProd Int Bool) :
    Except IntegrateError (ForInStep (MProd Int Bool)) := do
  let mut scanning := state.snd
  let mut destIdx := state.fst
  let i := (leftIdx + offset).toNat
  let other <- getElemExcept arr i
  let oLeftIdx <- findRefIdx other.toV2.origin arr
  let oRightIdx <- findRefIdx other.toV2.rightOrigin arr

  if oLeftIdx < leftIdx then
    return .done ⟨ destIdx, scanning ⟩
  else if oLeftIdx == leftIdx then
    if input.id.clientId > other.id.clientId then
      scanning := false
    else if oRightIdx == rightIdx then
      return .done ⟨ destIdx, scanning ⟩
    else
      scanning := true

  if !scanning then
    destIdx := i + 1

  return .yield ⟨ destIdx, scanning ⟩

def scanStepOld (arr : Array (YjsItem A)) (input : IntegrateInput A)
    (leftIdx rightIdx : Int) (offset : Nat) (state : MProd Int Bool) :
    Except IntegrateError (ForInStep (MProd Int Bool)) := do
  let mut scanning := state.snd
  let mut destIdx := state.fst
  let i := (leftIdx + offset).toNat
  let other <- getElemExcept arr i
  let oLeftIdx <- findPtrIdx other.origin arr
  let oRightIdx <- findPtrIdx other.rightOrigin arr

  if oLeftIdx < leftIdx then
    return .done ⟨ destIdx, scanning ⟩
  else if oLeftIdx == leftIdx then
    if input.id.clientId > other.id.clientId then
      scanning := false
    else if oRightIdx == rightIdx then
      return .done ⟨ destIdx, scanning ⟩
    else
      scanning := true

  if !scanning then
    destIdx := i + 1

  return .yield ⟨ destIdx, scanning ⟩

theorem forIn_list_congr {α β ε : Type} {lst : List α} {init : β}
    {f g : α → β → Except ε (ForInStep β)} :
    (∀ x s, f x s = g x s) ->
    forIn lst init f = forIn lst init g := by
  intro hfg
  induction lst generalizing init with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.forIn_cons, List.forIn_cons, hfg]
      cases h : g x init with
      | error e =>
          rfl
      | ok step =>
          cases step with
          | done b =>
              rfl
          | yield s =>
              simpa using ih (init := s)

theorem findRefIdx_toRefV2_eq_findPtrIdx
    {arr : Array (YjsItem A)} {ptr : YjsPtr A} :
    uniqueId arr.toList ->
    ArrSet arr.toList ptr ->
    findRefIdx ptr.toRefV2 arr = findPtrIdx ptr arr := by
  intro hUnique hPtrIn
  cases ptr with
  | first =>
      simp [findRefIdx, findPtrIdx, YjsPtr.toRefV2]
  | last =>
      simp [findRefIdx, findPtrIdx, YjsPtr.toRefV2]
  | itemPtr item =>
      simp [ArrSet] at hPtrIn
      have hFindIdx :
          Array.findIdx? (fun a => decide (a.id = item.id)) arr =
          Array.findIdx? (fun a => decide (a = item)) arr := by
        apply Array.findIdx?_pred_eq_eq
        intro a hAMem
        simp
        constructor
        · intro hEq
          exact uniqueId_id_eq_implies_eq hUnique _ _ hAMem hPtrIn hEq
        · intro hEq
          simp [hEq]
      unfold findRefIdx findPtrIdx
      simp [YjsPtr.toRefV2, hFindIdx]
      rfl

theorem findRefIdx_origin_eq_findPtrIdx
    {arr : Array (YjsItem A)} {item : YjsItem A} :
    YjsArrInvariant arr.toList ->
    item ∈ arr ->
    findRefIdx item.toV2.origin arr = findPtrIdx item.origin arr := by
  intro hArr hMem
  rcases item with ⟨ origin, rightOrigin, id, content ⟩
  simpa [YjsItem.toV2] using
    findRefIdx_toRefV2_eq_findPtrIdx (arr := arr) (ptr := origin)
      hArr.unique (by
        apply IsClosedItemSet.closedLeft
          (P := ArrSet arr.toList)
          (o := origin) (r := rightOrigin)
          (id := id) (c := content)
        exact hArr.closed
        simpa [ArrSet] using hMem)

theorem findRefIdx_rightOrigin_eq_findPtrIdx
    {arr : Array (YjsItem A)} {item : YjsItem A} :
    YjsArrInvariant arr.toList ->
    item ∈ arr ->
    findRefIdx item.toV2.rightOrigin arr = findPtrIdx item.rightOrigin arr := by
  intro hArr hMem
  rcases item with ⟨ origin, rightOrigin, id, content ⟩
  simpa [YjsItem.toV2] using
    findRefIdx_toRefV2_eq_findPtrIdx (arr := arr) (ptr := rightOrigin)
      hArr.unique (by
        apply IsClosedItemSet.closedRight
          (P := ArrSet arr.toList)
          (o := origin) (r := rightOrigin)
          (id := id) (c := content)
        exact hArr.closed
        simpa [ArrSet] using hMem)

omit [DecidableEq A] in theorem getElemExcept_mem
    {arr : Array (YjsItem A)} {i : Nat} {item : YjsItem A} :
    getElemExcept arr i = Except.ok item ->
    item ∈ arr := by
  intro hGet
  unfold getElemExcept at hGet
  cases hItem : arr[i]? with
  | none =>
      simp [hItem] at hGet
  | some found =>
      simp [hItem] at hGet
      cases hGet
      rw [Array.mem_iff_getElem]
      rw [Array.getElem?_eq_some_iff] at hItem
      exact ⟨ i, hItem.1, hItem.2 ⟩

theorem getElemExcept_findRefIdx_origin_eq_findPtrIdx
    {arr : Array (YjsItem A)} {i : Nat} {item : YjsItem A} :
    YjsArrInvariant arr.toList ->
    getElemExcept arr i = Except.ok item ->
    findRefIdx item.toV2.origin arr = findPtrIdx item.origin arr := by
  intro hArr hGet
  exact findRefIdx_origin_eq_findPtrIdx hArr (getElemExcept_mem hGet)

theorem getElemExcept_findRefIdx_rightOrigin_eq_findPtrIdx
    {arr : Array (YjsItem A)} {i : Nat} {item : YjsItem A} :
    YjsArrInvariant arr.toList ->
    getElemExcept arr i = Except.ok item ->
    findRefIdx item.toV2.rightOrigin arr = findPtrIdx item.rightOrigin arr := by
  intro hArr hGet
  exact findRefIdx_rightOrigin_eq_findPtrIdx hArr (getElemExcept_mem hGet)

theorem getElemExcept_lookupPairV2_eq_lookupPair
    {arr : Array (YjsItem A)} {i : Nat} {item : YjsItem A} :
    YjsArrInvariant arr.toList ->
    getElemExcept arr i = Except.ok item ->
    (do
      let oLeftIdx <- findRefIdx item.toV2.origin arr
      let oRightIdx <- findRefIdx item.toV2.rightOrigin arr
      return (oLeftIdx, oRightIdx)) =
    (do
      let oLeftIdx <- findPtrIdx item.origin arr
      let oRightIdx <- findPtrIdx item.rightOrigin arr
      return (oLeftIdx, oRightIdx)) := by
  intro hArr hGet
  rw [getElemExcept_findRefIdx_origin_eq_findPtrIdx hArr hGet]
  rw [getElemExcept_findRefIdx_rightOrigin_eq_findPtrIdx hArr hGet]

theorem scanStepV2_eq_scanStepOld
    {arr : Array (YjsItem A)} {input : IntegrateInput A}
    {leftIdx rightIdx : Int} {offset : Nat} {state : MProd Int Bool} :
    YjsArrInvariant arr.toList ->
    scanStepV2 arr input leftIdx rightIdx offset state =
      scanStepOld arr input leftIdx rightIdx offset state := by
  intro hArr
  unfold scanStepV2 scanStepOld
  cases hGet : getElemExcept arr ((leftIdx + offset).toNat) with
  | error err =>
      simp [hGet, bind, Except.bind]
  | ok other =>
      simp [hGet, bind, Except.bind]
      have hOrigin :
          findRefIdx other.toV2.origin arr = findPtrIdx other.origin arr := by
        exact getElemExcept_findRefIdx_origin_eq_findPtrIdx
          (arr := arr) (i := (leftIdx + offset).toNat) (item := other) hArr hGet
      have hRight :
          findRefIdx other.toV2.rightOrigin arr = findPtrIdx other.rightOrigin arr := by
        exact getElemExcept_findRefIdx_rightOrigin_eq_findPtrIdx
          (arr := arr) (i := (leftIdx + offset).toNat) (item := other) hArr hGet
      rw [show findRefIdx other.origin.toRefV2 arr = findPtrIdx other.origin arr by
        simpa [YjsItem.toV2] using hOrigin]
      rw [show findRefIdx other.rightOrigin.toRefV2 arr = findPtrIdx other.rightOrigin arr by
        simpa [YjsItem.toV2] using hRight]

theorem findIntegratedIndexV2_eq_findIntegratedIndex
    {arr : Array (YjsItem A)} {input : IntegrateInput A} {leftIdx rightIdx : Int} :
    YjsArrInvariant arr.toList ->
    findIntegratedIndexV2 leftIdx rightIdx input arr =
      findIntegratedIndex leftIdx rightIdx input arr := by
  intro hArr
  unfold findIntegratedIndexV2 findIntegratedIndex
  change
    (do
      let r ← forIn [1:(rightIdx - leftIdx).toNat] (⟨ leftIdx + 1, false ⟩ : MProd Int Bool)
        (scanStepV2 arr input leftIdx rightIdx)
      pure (Int.toNat r.fst)) =
    (do
      let r ← forIn [1:(rightIdx - leftIdx).toNat] (⟨ leftIdx + 1, false ⟩ : MProd Int Bool)
        (scanStepOld arr input leftIdx rightIdx)
      pure (Int.toNat r.fst))
  rw [Std.Range.forIn_eq_forIn_range', Std.Range.size]
  rw [Std.Range.forIn_eq_forIn_range', Std.Range.size]
  have hFor :
      forIn (List.range' 1 ((rightIdx - leftIdx).toNat - 1) 1)
          (⟨ leftIdx + 1, false ⟩ : MProd Int Bool)
          (scanStepV2 arr input leftIdx rightIdx) =
        forIn (List.range' 1 ((rightIdx - leftIdx).toNat - 1) 1)
          (⟨ leftIdx + 1, false ⟩ : MProd Int Bool)
          (scanStepOld arr input leftIdx rightIdx) := by
    apply forIn_list_congr
    intro offset state
    exact scanStepV2_eq_scanStepOld
      (arr := arr) (input := input) (leftIdx := leftIdx) (rightIdx := rightIdx)
      (offset := offset) (state := state) hArr
  simpa [bind, Except.bind] using
    congrArg (fun x => x >>= fun r => pure (Int.toNat r.fst)) hFor

theorem integrateV2Item_eq_integrateScan
    {arr : Array (YjsItem A)} {input : IntegrateInput A} :
    YjsArrInvariant arr.toList ->
    integrateV2Item input arr =
      (do
        let leftIdx <- findLeftIdx input.originId arr
        let rightIdx <- findRightIdx input.rightOriginId arr
        let destIdx <- findIntegratedIndex leftIdx rightIdx input arr
        let item <- mkItemV2ByIndex leftIdx rightIdx input arr
        pure (destIdx, item)) := by
  intro hArr
  unfold integrateV2Item
  cases hLeft : findLeftIdx input.originId arr with
  | error err =>
      simp [bind, Except.bind]
  | ok leftIdx =>
      simp [bind, Except.bind]
      cases hRight : findRightIdx input.rightOriginId arr with
      | error err =>
          simp
      | ok rightIdx =>
          simp
          rw [findIntegratedIndexV2_eq_findIntegratedIndex
            (arr := arr) (input := input) (leftIdx := leftIdx) (rightIdx := rightIdx) hArr]
