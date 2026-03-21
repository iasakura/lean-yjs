import LeanYjs.Indirect.Algorithm.Insert.Basic
import LeanYjs.Indirect.Algorithm.Delete.Basic
import LeanYjs.Algorithm.Delete.Basic
import LeanYjs.Algorithm.Insert.Lemmas
import LeanYjs.Algorithm.Invariant.YjsArray
import Mathlib.Data.List.InsertIdx

namespace Indirect

variable {A : Type} [DecidableEq A]

def StateEquivalent (direct : _root_.YjsState A) (indirect : YjsState A) : Prop :=
  ofDirectState direct = indirect

theorem deleteById_ofDirectState (state : _root_.YjsState A) (id : YjsId) :
    deleteById (ofDirectState state) id = ofDirectState (_root_.deleteById state id) := by
  rfl

theorem findLeftIdx_ofDirect (originId : Option YjsId) (arr : Array (_root_.YjsItem A)) :
    findLeftIdx originId (arr.map ofDirectItem) = _root_.findLeftIdx originId arr := by
  cases originId with
  | none =>
      simp [findLeftIdx, _root_.findLeftIdx]
  | some id =>
      simp [findLeftIdx, _root_.findLeftIdx]
      have h_eq :
          Array.findIdx? ((fun item => decide (item.id = id)) ∘ ofDirectItem) arr =
            Array.findIdx? (fun item => decide (item.id = id)) arr := by
        rw [Array.findIdx?_pred_eq_eq]
        intro a h_a_mem
        simp [Function.comp, ofDirectItem]
      rw [h_eq]
      rfl

theorem findRightIdx_ofDirect (rightOriginId : Option YjsId) (arr : Array (_root_.YjsItem A)) :
    findRightIdx rightOriginId (arr.map ofDirectItem) = _root_.findRightIdx rightOriginId arr := by
  cases rightOriginId with
  | none =>
      simp [findRightIdx, _root_.findRightIdx]
  | some id =>
      simp [findRightIdx, _root_.findRightIdx]
      have h_eq :
          Array.findIdx? ((fun item => decide (item.id = id)) ∘ ofDirectItem) arr =
            Array.findIdx? (fun item => decide (item.id = id)) arr := by
        rw [Array.findIdx?_pred_eq_eq]
        intro a h_a_mem
        simp [Function.comp, ofDirectItem]
      rw [h_eq]
      rfl

theorem isClockSafe_ofDirect (id : YjsId) (arr : Array (_root_.YjsItem A)) :
    isClockSafe id (arr.map ofDirectItem) = _root_.isClockSafe id arr := by
  simp [isClockSafe, _root_.isClockSafe, ofDirectItem]

theorem ofDirectPtr_eq_ofOriginId {arr : Array (_root_.YjsItem A)} {originId : Option YjsId}
    {ptr : _root_.YjsPtr A} :
    _root_.isLeftIdPtr arr originId ptr →
      YjsRef.ofDirectPtr ptr = YjsRef.ofOriginId originId := by
  intro h_ptr
  cases h_originId : originId with
  | none =>
      simp [_root_.isLeftIdPtr, h_originId, YjsRef.ofOriginId] at h_ptr ⊢
      simp [h_ptr, YjsRef.ofDirectPtr]
  | some oid =>
      simp [_root_.isLeftIdPtr, h_originId, YjsRef.ofOriginId] at h_ptr ⊢
      rcases h_ptr with ⟨ item, h_ptr_eq, h_find ⟩
      rw [Array.find?_eq_some_iff_getElem] at h_find
      obtain ⟨ h_id_eq, _, _, _, _ ⟩ := h_find
      subst h_ptr_eq
      have h_id_eq' : item.id = oid := by
        simpa using h_id_eq
      simpa [YjsRef.ofDirectPtr] using congrArg YjsRef.itemId h_id_eq'

theorem ofDirectPtr_eq_ofRightOriginId {arr : Array (_root_.YjsItem A)} {rightOriginId : Option YjsId}
    {ptr : _root_.YjsPtr A} :
    _root_.isRightIdPtr arr rightOriginId ptr →
      YjsRef.ofDirectPtr ptr = YjsRef.ofRightOriginId rightOriginId := by
  intro h_ptr
  cases h_rightId : rightOriginId with
  | none =>
      simp [_root_.isRightIdPtr, h_rightId, YjsRef.ofRightOriginId] at h_ptr ⊢
      simp [h_ptr, YjsRef.ofDirectPtr]
  | some rid =>
      simp [_root_.isRightIdPtr, h_rightId, YjsRef.ofRightOriginId] at h_ptr ⊢
      rcases h_ptr with ⟨ item, h_ptr_eq, h_find ⟩
      rw [Array.find?_eq_some_iff_getElem] at h_find
      obtain ⟨ h_id_eq, _, _, _, _ ⟩ := h_find
      subst h_ptr_eq
      have h_id_eq' : item.id = rid := by
        simpa using h_id_eq
      simpa [YjsRef.ofDirectPtr] using congrArg YjsRef.itemId h_id_eq'

theorem ofDirectItem_mkItemByIndex (arr : Array (_root_.YjsItem A)) (input : IntegrateInput A)
    (leftIdx rightIdx : Int)
    (h_left : _root_.findLeftIdx input.originId arr = Except.ok leftIdx)
    (h_right : _root_.findRightIdx input.rightOriginId arr = Except.ok rightIdx) :
    Except.map ofDirectItem (_root_.mkItemByIndex leftIdx rightIdx input arr) =
      Except.ok (mkItem input) := by
  obtain ⟨ leftPtr, h_getLeft, h_leftPtr ⟩ :=
    _root_.findLeftIdx_getElemExcept (arr := arr) (input := input) h_left
  obtain ⟨ rightPtr, h_getRight, h_rightPtr ⟩ :=
    _root_.findRightIdx_getElemExcept (arr := arr) (input := input) h_right
  simp [_root_.mkItemByIndex, h_getLeft, h_getRight, mkItem, Except.map, bind, Except.bind,
    ofDirectItem, pure, Except.pure]
  rw [ofDirectPtr_eq_ofOriginId h_leftPtr, ofDirectPtr_eq_ofRightOriginId h_rightPtr]
  constructor <;> rfl

private def scanStepDirect (leftIdx rightIdx : Int) (input : IntegrateInput A)
    (arr : Array (_root_.YjsItem A)) (offset : Nat) (r : MProd Int Bool) :
    Except IntegrateError (ForInStep (MProd Int Bool)) := do
  let other <- _root_.getElemExcept arr (leftIdx + offset).toNat
  let oLeftIdx <- _root_.findPtrIdx other.origin arr
  let oRightIdx <- _root_.findPtrIdx other.rightOrigin arr
  if oLeftIdx < leftIdx then
    pure (ForInStep.done ⟨ r.fst, r.snd ⟩)
  else if oLeftIdx = leftIdx then
    if other.id.clientId < input.id.clientId then
      pure (ForInStep.yield ⟨ max (leftIdx + offset) 0 + 1, false ⟩)
    else if oRightIdx = rightIdx then
      pure (ForInStep.done ⟨ r.fst, r.snd ⟩)
    else
      pure (ForInStep.yield ⟨ r.fst, true ⟩)
  else if r.snd = false then
    pure (ForInStep.yield ⟨ max (leftIdx + offset) 0 + 1, r.snd ⟩)
  else
    pure (ForInStep.yield ⟨ r.fst, r.snd ⟩)

private def scanStepIndirect (leftIdx rightIdx : Int) (input : IntegrateInput A)
    (arr : Array (_root_.YjsItem A)) (offset : Nat) (r : MProd Int Bool) :
    Except IntegrateError (ForInStep (MProd Int Bool)) := do
  let other <- getElemExcept (arr.map ofDirectItem) (leftIdx + offset).toNat
  let oLeftIdx <- findRefIdx other.origin (arr.map ofDirectItem)
  let oRightIdx <- findRefIdx other.rightOrigin (arr.map ofDirectItem)
  if oLeftIdx < leftIdx then
    pure (ForInStep.done ⟨ r.fst, r.snd ⟩)
  else if oLeftIdx = leftIdx then
    if other.id.clientId < input.id.clientId then
      pure (ForInStep.yield ⟨ max (leftIdx + offset) 0 + 1, false ⟩)
    else if oRightIdx = rightIdx then
      pure (ForInStep.done ⟨ r.fst, r.snd ⟩)
    else
      pure (ForInStep.yield ⟨ r.fst, true ⟩)
  else if r.snd = false then
    pure (ForInStep.yield ⟨ max (leftIdx + offset) 0 + 1, r.snd ⟩)
  else
    pure (ForInStep.yield ⟨ r.fst, r.snd ⟩)

theorem findRefIdx_ofDirectPtr_exact (arr : Array (_root_.YjsItem A)) (ptr : _root_.YjsPtr A)
    (h_unique : _root_.uniqueId arr.toList) (h_ptr : _root_.ArrSet arr.toList ptr) :
    findRefIdx (YjsRef.ofDirectPtr ptr) (arr.map ofDirectItem) = _root_.findPtrIdx ptr arr := by
  cases ptr with
  | first =>
      simp [findRefIdx, YjsRef.ofDirectPtr, _root_.findPtrIdx]
  | last =>
      simp [findRefIdx, YjsRef.ofDirectPtr, _root_.findPtrIdx]
  | itemPtr item =>
      simp [_root_.ArrSet] at h_ptr
      simp [findRefIdx, YjsRef.ofDirectPtr, _root_.findPtrIdx]
      have h_eq :
          Array.findIdx? ((fun i => decide (i.id = item.id)) ∘ ofDirectItem) arr =
            Array.findIdx? (fun i => decide (i = item)) arr := by
        rw [Array.findIdx?_pred_eq_eq]
        intro a h_a_mem
        simp [Function.comp]
        constructor
        . intro h_id_eq
          have h := _root_.uniqueId_id_eq_implies_eq h_unique _ _ h_ptr h_a_mem h_id_eq.symm
          simp [h]
        . intro h_item_eq
          simp [h_item_eq, ofDirectItem]
      rw [h_eq]
      rfl

theorem scanStep_ofDirect (leftIdx rightIdx : Int) (input : IntegrateInput A)
    (arr : Array (_root_.YjsItem A)) (offset : Nat) (r : MProd Int Bool)
    (harrinv : _root_.YjsArrInvariant arr.toList) :
    scanStepIndirect leftIdx rightIdx input arr offset r =
      scanStepDirect leftIdx rightIdx input arr offset r := by
  simp [scanStepIndirect, scanStepDirect, getElemExcept, _root_.getElemExcept]
  cases hGet : arr[(leftIdx + offset).toNat]? with
  | none =>
      rfl
  | some other =>
      simp
      have h_mem : other ∈ arr := by
        rw [Array.mem_iff_getElem]
        rw [Array.getElem?_eq_some_iff] at hGet
        exact ⟨ (leftIdx + offset).toNat, hGet.1, hGet.2 ⟩
      have h_other_in : _root_.ArrSet arr.toList (_root_.YjsPtr.itemPtr other) := by
        simp [_root_.ArrSet, h_mem]
      have h_origin_in : _root_.ArrSet arr.toList other.origin := by
        obtain ⟨ o, r, id, c ⟩ := other
        exact harrinv.closed.closedLeft o r id c h_other_in
      have h_right_in : _root_.ArrSet arr.toList other.rightOrigin := by
        obtain ⟨ o, r, id, c ⟩ := other
        exact harrinv.closed.closedRight o r id c h_other_in
      have h_left_eq :
          findRefIdx (ofDirectItem other).origin (arr.map ofDirectItem) =
            _root_.findPtrIdx other.origin arr := by
        simpa [ofDirectItem] using findRefIdx_ofDirectPtr_exact arr other.origin harrinv.unique h_origin_in
      have h_right_eq :
          findRefIdx (ofDirectItem other).rightOrigin (arr.map ofDirectItem) =
            _root_.findPtrIdx other.rightOrigin arr := by
        simpa [ofDirectItem] using findRefIdx_ofDirectPtr_exact arr other.rightOrigin harrinv.unique h_right_in
      rw [h_left_eq, h_right_eq]
      rfl

theorem forIn_offsets_ofDirect_expanded (leftIdx rightIdx : Int) (input : IntegrateInput A)
    (arr : Array (_root_.YjsItem A)) (offsets : List Nat) (r : MProd Int Bool)
    (harrinv : _root_.YjsArrInvariant arr.toList) :
    forIn offsets r (fun offset r => do
      let other <- getElemExcept (arr.map ofDirectItem) (leftIdx + offset).toNat
      let oLeftIdx <- findRefIdx other.origin (arr.map ofDirectItem)
      let oRightIdx <- findRefIdx other.rightOrigin (arr.map ofDirectItem)
      if oLeftIdx < leftIdx then
        pure (ForInStep.done (MProd.mk r.fst r.snd))
      else if oLeftIdx = leftIdx then
        if other.id.clientId < input.id.clientId then
          pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) false))
        else if oRightIdx = rightIdx then
          pure (ForInStep.done (MProd.mk r.fst r.snd))
        else
          pure (ForInStep.yield (MProd.mk r.fst true))
      else if r.snd = false then
        pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) r.snd))
      else
        pure (ForInStep.yield (MProd.mk r.fst r.snd))) =
    forIn offsets r (fun offset r => do
      let other <- _root_.getElemExcept arr (leftIdx + offset).toNat
      let oLeftIdx <- _root_.findPtrIdx other.origin arr
      let oRightIdx <- _root_.findPtrIdx other.rightOrigin arr
      if oLeftIdx < leftIdx then
        pure (ForInStep.done (MProd.mk r.fst r.snd))
      else if oLeftIdx = leftIdx then
        if other.id.clientId < input.id.clientId then
          pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) false))
        else if oRightIdx = rightIdx then
          pure (ForInStep.done (MProd.mk r.fst r.snd))
        else
          pure (ForInStep.yield (MProd.mk r.fst true))
      else if r.snd = false then
        pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) r.snd))
      else
        pure (ForInStep.yield (MProd.mk r.fst r.snd))) := by
  induction offsets generalizing r with
  | nil =>
      simp [List.forIn_nil]
  | cons offset offsets ih =>
      rw [List.forIn_cons, List.forIn_cons]
      have hstep :
          (do
            let other <- getElemExcept (arr.map ofDirectItem) (leftIdx + offset).toNat
            let oLeftIdx <- findRefIdx other.origin (arr.map ofDirectItem)
            let oRightIdx <- findRefIdx other.rightOrigin (arr.map ofDirectItem)
            if oLeftIdx < leftIdx then
              pure (ForInStep.done (MProd.mk r.fst r.snd))
            else if oLeftIdx = leftIdx then
              if other.id.clientId < input.id.clientId then
                pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) false))
              else if oRightIdx = rightIdx then
                pure (ForInStep.done (MProd.mk r.fst r.snd))
              else
                pure (ForInStep.yield (MProd.mk r.fst true))
            else if r.snd = false then
              pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) r.snd))
            else
              pure (ForInStep.yield (MProd.mk r.fst r.snd))) =
          (do
            let other <- _root_.getElemExcept arr (leftIdx + offset).toNat
            let oLeftIdx <- _root_.findPtrIdx other.origin arr
            let oRightIdx <- _root_.findPtrIdx other.rightOrigin arr
            if oLeftIdx < leftIdx then
              pure (ForInStep.done (MProd.mk r.fst r.snd))
            else if oLeftIdx = leftIdx then
              if other.id.clientId < input.id.clientId then
                pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) false))
              else if oRightIdx = rightIdx then
                pure (ForInStep.done (MProd.mk r.fst r.snd))
              else
                pure (ForInStep.yield (MProd.mk r.fst true))
            else if r.snd = false then
              pure (ForInStep.yield (MProd.mk (max (leftIdx + offset) 0 + 1) r.snd))
            else
              pure (ForInStep.yield (MProd.mk r.fst r.snd))) := by
        simpa [scanStepIndirect, scanStepDirect] using scanStep_ofDirect leftIdx rightIdx input arr offset r harrinv
      rw [hstep]
      cases hres : scanStepDirect leftIdx rightIdx input arr offset r <;> simp [ih, harrinv]

theorem findIntegratedIndex_ofDirect (leftIdx rightIdx : Int) (input : IntegrateInput A)
    (arr : Array (_root_.YjsItem A)) (harrinv : _root_.YjsArrInvariant arr.toList) :
    findIntegratedIndex leftIdx rightIdx input (arr.map ofDirectItem) =
      _root_.findIntegratedIndex leftIdx rightIdx input arr := by
  simp [findIntegratedIndex, _root_.findIntegratedIndex]
  exact congrArg (fun x => (fun a => a.fst.toNat) <$> x)
    (forIn_offsets_ofDirect_expanded leftIdx rightIdx input arr
      (List.range' 1 ((rightIdx - leftIdx).toNat - 1)) (MProd.mk (leftIdx + 1) false) harrinv)

theorem map_ofDirectItem_insertIdxIfInBounds (arr : Array (_root_.YjsItem A)) (i : Nat)
    (item : _root_.YjsItem A) :
    Array.map ofDirectItem (arr.insertIdxIfInBounds i item) =
      (arr.map ofDirectItem).insertIdxIfInBounds i (ofDirectItem item) := by
  rw [← Array.toList_inj]
  by_cases h : i ≤ arr.size
  . simp [Array.insertIdxIfInBounds, h, List.map_insertIdx]
  . simp [Array.insertIdxIfInBounds, h]

theorem integrate_ofDirect (arr : Array (_root_.YjsItem A)) (input : IntegrateInput A)
    (harrinv : _root_.YjsArrInvariant arr.toList) :
    integrate input (arr.map ofDirectItem) = Except.map (Array.map ofDirectItem) (_root_.integrate input arr) := by
  cases h_left : _root_.findLeftIdx input.originId arr with
  | error err =>
      simp [integrate, _root_.integrate, findLeftIdx_ofDirect, h_left, Except.map, bind, Except.bind]
  | ok leftIdx =>
      cases h_right : _root_.findRightIdx input.rightOriginId arr with
      | error err =>
          simp [integrate, _root_.integrate, findLeftIdx_ofDirect, findRightIdx_ofDirect, h_left, h_right,
            Except.map, bind, Except.bind]
      | ok rightIdx =>
          simp [integrate, _root_.integrate, findLeftIdx_ofDirect, findRightIdx_ofDirect, h_left, h_right,
            Except.map, bind, Except.bind]
          rw [findIntegratedIndex_ofDirect leftIdx rightIdx input arr harrinv]
          cases h_dest : _root_.findIntegratedIndex leftIdx rightIdx input arr with
          | error err =>
              simp [h_dest]
          | ok destIdx =>
              cases h_item : _root_.mkItemByIndex leftIdx rightIdx input arr with
              | error err =>
                  have h_mk := ofDirectItem_mkItemByIndex arr input leftIdx rightIdx h_left h_right
                  simp [Except.map, h_item] at h_mk
              | ok item =>
                  have h_mk := ofDirectItem_mkItemByIndex arr input leftIdx rightIdx h_left h_right
                  simp [Except.map, h_item] at h_mk
                  simp [pure, Except.pure]
                  rw [map_ofDirectItem_insertIdxIfInBounds]
                  simpa [h_mk]

theorem integrateSafe_ofDirect (arr : Array (_root_.YjsItem A)) (input : IntegrateInput A)
    (harrinv : _root_.YjsArrInvariant arr.toList) :
    integrateSafe input (arr.map ofDirectItem) =
      Except.map (Array.map ofDirectItem) (_root_.integrateSafe input arr) := by
  simp [integrateSafe, _root_.integrateSafe, isClockSafe_ofDirect]
  split
  . simpa using integrate_ofDirect arr input harrinv
  . rfl

theorem insert_ofDirectState (state : _root_.YjsState A) (input : IntegrateInput A)
    (hinv : _root_.YjsStateInvariant state) :
    YjsState.insert (ofDirectState state) input = Except.map ofDirectState (_root_.YjsState.insert state input) := by
  have h_arrinv : _root_.YjsArrInvariant state.items.toList := by
    simpa [_root_.YjsStateInvariant] using hinv
  simp [YjsState.insert, _root_.YjsState.insert, ofDirectState, Except.map, bind, Except.bind,
    pure, Except.pure]
  rw [integrateSafe_ofDirect state.items input h_arrinv]
  cases h_integrate : _root_.integrateSafe input state.items <;> simp [Except.map, h_integrate]

theorem insert_preserves_stateEquivalent {direct direct' : _root_.YjsState A}
    {indirect indirect' : YjsState A} {input : IntegrateInput A}
    (h_eq : StateEquivalent direct indirect)
    (h_inv : _root_.YjsStateInvariant direct)
    (h_direct : _root_.YjsState.insert direct input = Except.ok direct')
    (h_indirect : YjsState.insert indirect input = Except.ok indirect') :
    StateEquivalent direct' indirect' := by
  subst h_eq
  rw [insert_ofDirectState direct input h_inv] at h_indirect
  rw [h_direct] at h_indirect
  have h_eq' : ofDirectState direct' = indirect' := by
    simpa [Except.map] using h_indirect
  simpa [StateEquivalent] using h_eq'

theorem delete_preserves_stateEquivalent {direct direct' : _root_.YjsState A}
    {indirect indirect' : YjsState A} {id : YjsId}
    (h_eq : StateEquivalent direct indirect)
    (h_direct : _root_.deleteById direct id = direct')
    (h_indirect : deleteById indirect id = indirect') :
    StateEquivalent direct' indirect' := by
  subst h_eq
  subst h_direct
  rw [deleteById_ofDirectState] at h_indirect
  simpa [StateEquivalent] using h_indirect

end Indirect
