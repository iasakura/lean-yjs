import LeanYjs.Algorithm.Insert.BasicV2
import LeanYjs.Algorithm.Invariant.YjsArray

variable {A : Type} [DecidableEq A]

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
