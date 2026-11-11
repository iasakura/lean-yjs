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

omit [DecidableEq A] in
theorem getElemExcept_ofDirect (arr : Array (_root_.YjsItem A)) (i : Nat) :
    getElemExcept (arr.map ofDirectItem) i = ofDirectItem <$> _root_.getElemExcept arr i := by
  simp only [getElemExcept, _root_.getElemExcept, Array.getElem?_map]
  cases arr[i]? <;> rfl

omit [DecidableEq A] in
@[simp] theorem id?_ofDirectPtr (p : _root_.YjsPtr A) :
    (YjsRef.ofDirectPtr p).id? = p.id? := by
  cases p <;> rfl

omit [DecidableEq A] in
/-- The two scans agree: the loop body only inspects ids, which `ofDirectItem`
preserves. -/
theorem findIntegratedIndex_ofDirect (leftIdx rightIdx : Int) (input : IntegrateInput A)
    (arr : Array (_root_.YjsItem A)) (_harrinv : _root_.YjsArrInvariant arr.toList) :
    findIntegratedIndex leftIdx rightIdx input (arr.map ofDirectItem) =
      _root_.findIntegratedIndex leftIdx rightIdx input arr := by
  unfold findIntegratedIndex _root_.findIntegratedIndex
  dsimp only
  congr 1
  congr 1
  funext offset r
  dsimp only
  rw [getElemExcept_ofDirect, bind_map_left]
  congr 1
  funext other
  simp only [ofDirectItem, id?_ofDirectPtr]

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
