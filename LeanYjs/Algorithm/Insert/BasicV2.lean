import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.ItemBridgeV2

variable {A : Type} [DecidableEq A]

def IntegrateInput.toItemV2 (input : IntegrateInput A) (arr : Array (YjsItem A)) :
    Except IntegrateError (YjsItemV2 A) := do
  let originRef <- match input.originId with
    | some id =>
      match arr.find? (fun item => item.id = id) with
      | some _ => Except.ok (.idRef id)
      | none => Except.error IntegrateError.error
    | none => Except.ok .first

  let rightOriginRef <- match input.rightOriginId with
    | some id =>
      match arr.find? (fun item => item.id = id) with
      | some _ => Except.ok (.idRef id)
      | none => Except.error IntegrateError.error
    | none => Except.ok .last

  return YjsItemV2.mk originRef rightOriginRef input.id input.content

def getRefExcept (arr : Array (YjsItem A)) (idx : Int) : Except IntegrateError ItemRef :=
  if idx = -1 then
    Except.ok .first
  else if idx = arr.size then
    Except.ok .last
  else
    match arr[idx.toNat]? with
    | some item => Except.ok item.toV2.toRef
    | none => Except.error IntegrateError.error

def mkItemV2ByIndex (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) :
    Except IntegrateError (YjsItemV2 A) := do
  return YjsItemV2.mk (← getRefExcept arr leftIdx) (← getRefExcept arr rightIdx) input.id input.content

def findRefIdx (ref : ItemRef) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match ref with
  | .idRef id =>
    match arr.findIdx? (fun item => item.id = id) with
    | some idx => return idx
    | none => Except.error IntegrateError.error
  | .first => return -1
  | .last => return arr.size

def findIntegratedIndexV2 (leftIdx rightIdx : Int) (newItem : IntegrateInput A)
    (arr : Array (YjsItem A)) : Except IntegrateError Nat := do
  let mut scanning := false
  let mut destIdx := leftIdx + 1
  for offset in [1:(rightIdx-leftIdx).toNat] do
    let i := (leftIdx + offset).toNat
    let other <- getElemExcept arr i

    let oLeftIdx <- findRefIdx other.toV2.origin arr
    let oRightIdx <- findRefIdx other.toV2.rightOrigin arr

    if oLeftIdx < leftIdx then
      break
    else if oLeftIdx == leftIdx then
      if newItem.id.clientId > other.id.clientId then
        scanning := false
      else if oRightIdx == rightIdx then
        break
      else
        scanning := true

    if !scanning then
      destIdx := i + 1

  return Int.toNat destIdx

def integrateV2Item (newItem : IntegrateInput A) (arr : Array (YjsItem A)) :
    Except IntegrateError (Nat × YjsItemV2 A) := do
  let leftIdx <- findLeftIdx newItem.originId arr
  let rightIdx <- findRightIdx newItem.rightOriginId arr
  let destIdx <- findIntegratedIndexV2 leftIdx rightIdx newItem arr
  let item <- mkItemV2ByIndex leftIdx rightIdx newItem arr
  return (destIdx, item)

omit [DecidableEq A] in private theorem find_item_id_eq
    {arr : Array (YjsItem A)} {targetId : YjsId} {item : YjsItem A} :
    arr.find? (fun cand => cand.id = targetId) = some item ->
    item.id = targetId := by
  intro hFind
  rw [Array.find?_eq_some_iff_getElem] at hFind
  simp at hFind
  obtain ⟨ hId, _, _, _, _ ⟩ := hFind
  exact hId

theorem IntegrateInput.toItem_toItemV2
    {input : IntegrateInput A} {arr : Array (YjsItem A)} {item : YjsItem A} :
    input.toItem arr = Except.ok item ->
    input.toItemV2 arr = Except.ok item.toV2 := by
  intro hToItem
  cases hOriginId : input.originId with
  | none =>
      cases hRightId : input.rightOriginId with
      | none =>
          simp [IntegrateInput.toItem, IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
            hOriginId, hRightId, YjsItem.toV2] at hToItem ⊢
          cases hToItem
          simp [YjsItem.toV2, YjsPtr.toRefV2]
      | some rightId =>
          cases hFindRight : arr.find? (fun item => item.id = rightId) with
          | none =>
              have : False := by
                simpa [IntegrateInput.toItem, bind, Except.bind, pure, Except.pure,
                  hOriginId, hRightId, hFindRight] using hToItem
              exact False.elim this
          | some rightItem =>
              have hRightEq : rightItem.id = rightId := find_item_id_eq hFindRight
              simp [IntegrateInput.toItem, IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                hOriginId, hRightId, hFindRight, YjsItem.toV2, hRightEq] at hToItem ⊢
              cases hToItem
              simp [YjsItem.toV2, YjsPtr.toRefV2, hRightEq]
  | some originId =>
      cases hFindOrigin : arr.find? (fun item => item.id = originId) with
      | none =>
          have : False := by
            simpa [IntegrateInput.toItem, bind, Except.bind, pure, Except.pure,
              hOriginId, hFindOrigin] using hToItem
          exact False.elim this
      | some originItem =>
          have hOriginEq : originItem.id = originId := find_item_id_eq hFindOrigin
          cases hRightId : input.rightOriginId with
          | none =>
              simp [IntegrateInput.toItem, IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                hOriginId, hRightId, hFindOrigin, YjsItem.toV2, hOriginEq] at hToItem ⊢
              cases hToItem
              simp [YjsItem.toV2, YjsPtr.toRefV2, hOriginEq]
          | some rightId =>
              cases hFindRight : arr.find? (fun item => item.id = rightId) with
              | none =>
                  have : False := by
                    simpa [IntegrateInput.toItem, bind, Except.bind, pure, Except.pure,
                      hOriginId, hRightId, hFindOrigin, hFindRight] using hToItem
                  exact False.elim this
              | some rightItem =>
                  have hRightEq : rightItem.id = rightId := find_item_id_eq hFindRight
                  simp [IntegrateInput.toItem, IntegrateInput.toItemV2, bind, Except.bind, pure, Except.pure,
                    hOriginId, hRightId, hFindOrigin, hFindRight, YjsItem.toV2, hOriginEq, hRightEq] at hToItem ⊢
                  cases hToItem
                  simp [YjsItem.toV2, YjsPtr.toRefV2, hOriginEq, hRightEq]

theorem getPtrExcept_toRefExcept
    {arr : Array (YjsItem A)} {idx : Int} {ptr : YjsPtr A} :
    getPtrExcept arr idx = Except.ok ptr ->
    getRefExcept arr idx = Except.ok ptr.toRefV2 := by
  intro hPtr
  by_cases hFirst : idx = -1
  · simp [getPtrExcept, getRefExcept, hFirst] at hPtr ⊢
    cases hPtr
    rfl
  · by_cases hLast : idx = arr.size
    · simp [getPtrExcept, getRefExcept, hFirst, hLast] at hPtr ⊢
      cases hPtr
      rfl
    · simp [getPtrExcept, getRefExcept, hFirst, hLast] at hPtr ⊢
      cases hItem : arr[idx.toNat]? with
      | none =>
          have : False := by
            simpa [hItem] using hPtr
          exact False.elim this
      | some item =>
          simp [hItem] at hPtr
          cases hPtr
          simp [YjsItem.toV2]

theorem findRefIdx_eq_ok_inj {arr : Array (YjsItem A)} (x y : ItemRef) :
    findRefIdx x arr = Except.ok i ->
    findRefIdx y arr = Except.ok i ->
    x = y := by
  intro hEqX hEqY
  cases x with
  | first =>
      cases y with
      | first =>
          simp
      | last =>
          simp [findRefIdx] at hEqX hEqY
          cases hEqX
          cases hEqY
      | idRef y =>
          exfalso
          simp [findRefIdx] at hEqX hEqY
          generalize hFind : Array.findIdx? (fun item => decide (item.id = y)) arr = idx at *
          cases idx <;> cases hEqY
          cases hEqX
  | last =>
      cases y with
      | first =>
          simp [findRefIdx] at hEqX hEqY
          cases hEqX
          cases hEqY
      | last =>
          simp
      | idRef y =>
          exfalso
          simp [findRefIdx] at hEqX hEqY
          generalize hFind : Array.findIdx? (fun item => decide (item.id = y)) arr = idx at *
          cases idx <;> cases hEqY
          cases hEqX
          rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hFind
          omega
  | idRef xId =>
      cases y with
      | first =>
          exfalso
          simp [findRefIdx] at hEqX hEqY
          generalize hFind : Array.findIdx? (fun item => decide (item.id = xId)) arr = idx at *
          cases idx <;> cases hEqX
          cases hEqY
      | last =>
          exfalso
          simp [findRefIdx] at hEqX hEqY
          generalize hFind : Array.findIdx? (fun item => decide (item.id = xId)) arr = idx at *
          cases idx <;> cases hEqX
          cases hEqY
          rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hFind
          omega
      | idRef yId =>
          simp [findRefIdx] at hEqX hEqY
          generalize hFindX : Array.findIdx? (fun item => decide (item.id = xId)) arr = idxX at *
          generalize hFindY : Array.findIdx? (fun item => decide (item.id = yId)) arr = idxY at *
          cases idxX <;> cases hEqX
          cases idxY <;> cases hEqY
          rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hFindX
          rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hFindY
          obtain ⟨ hLtX, hEqX' ⟩ := hFindX
          obtain ⟨ hLtY, hEqY' ⟩ := hFindY
          rw [Array.findIdx_eq hLtX] at hEqX'
          rw [Array.findIdx_eq hLtY] at hEqY'
          simp at hEqX' hEqY'
          obtain ⟨ hIdX, _ ⟩ := hEqX'
          obtain ⟨ hIdY, _ ⟩ := hEqY'
          subst xId yId
          simp

theorem mkItemByIndex_toV2
    {leftIdx rightIdx : Int} {input : IntegrateInput A} {arr : Array (YjsItem A)} {item : YjsItem A} :
    mkItemByIndex leftIdx rightIdx input arr = Except.ok item ->
    mkItemV2ByIndex leftIdx rightIdx input arr = Except.ok item.toV2 := by
  intro hItem
  unfold mkItemByIndex at hItem
  cases hLeft : getPtrExcept arr leftIdx with
  | error err =>
      have : False := by
        simpa [bind, Except.bind, pure, Except.pure, hLeft] using hItem
      exact False.elim this
  | ok leftPtr =>
      cases hRight : getPtrExcept arr rightIdx with
      | error err =>
          have : False := by
            simpa [bind, Except.bind, pure, Except.pure, hLeft, hRight] using hItem
          exact False.elim this
      | ok rightPtr =>
          simp [bind, Except.bind, pure, Except.pure, hLeft, hRight] at hItem
          cases hItem
          have hLeftV2 :
              getRefExcept arr leftIdx = Except.ok leftPtr.toRefV2 :=
            getPtrExcept_toRefExcept hLeft
          have hRightV2 :
              getRefExcept arr rightIdx = Except.ok rightPtr.toRefV2 :=
            getPtrExcept_toRefExcept hRight
          simp [mkItemV2ByIndex, bind, Except.bind, pure, Except.pure, hLeftV2, hRightV2, YjsItem.toV2]

open Std.Do

@[spec] theorem findRefIdx_spec (ref : ItemRef) (arr : Array (YjsItem A)) :
    ⦃⌜True⌝⦄ findRefIdx ref arr
    ⦃post⟨fun idx => ⌜(-1 : Int) ≤ idx ∧ idx ≤ arr.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [findRefIdx]
  all_goals mleave
  case vc1.h_1.h_1 =>
    rename_i idx h_find
    rw [Array.findIdx?_eq_some_iff_getElem] at h_find
    obtain ⟨ h_lt, _, _ ⟩ := h_find
    constructor
    · have h_nonneg : (0 : Int) ≤ (idx : Int) := by
        exact_mod_cast (Nat.zero_le idx)
      omega
    · exact_mod_cast (Nat.le_of_lt h_lt)
  case vc3.h_2 =>
    constructor
    · omega
    · have h_nonneg : (0 : Int) ≤ arr.size := by
        exact_mod_cast (Nat.zero_le arr.size)
      omega
  case vc4.h_3 =>
    constructor
    · have h_nonneg : (0 : Int) ≤ arr.size := by
        exact_mod_cast (Nat.zero_le arr.size)
      omega
    · omega

@[spec] theorem getRefExcept_spec (arr : Array (YjsItem A)) (idx : Int) :
    ⦃⌜(-1 : Int) ≤ idx ∧ idx ≤ arr.size⌝⦄ getRefExcept arr idx
    ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [getRefExcept]
  all_goals mleave
  case vc4.isFalse.isFalse.h_2 =>
    intro h_low h_high
    have h_nonneg : (0 : Int) ≤ idx := by
      omega
    have h_lt : idx < arr.size := by
      omega
    have h_nat_lt : idx.toNat < arr.size := (Int.toNat_lt h_nonneg).2 h_lt
    have h_some : arr[idx.toNat]? = some arr[idx.toNat] := by
      exact (Array.getElem?_eq_some_iff).2 ⟨ h_nat_lt, rfl ⟩
    have h_none : arr[idx.toNat]? = none := by assumption
    simp [h_none] at h_some

@[spec] theorem mkItemV2ByIndex_spec
    (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) :
    ⦃⌜(-1 : Int) ≤ leftIdx ∧ leftIdx ≤ arr.size ∧ (-1 : Int) ≤ rightIdx ∧ rightIdx ≤ arr.size⌝⦄
      mkItemV2ByIndex leftIdx rightIdx input arr
    ⦃post⟨fun item => ⌜item.id = input.id⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [mkItemV2ByIndex, getRefExcept_spec]
  all_goals mleave
  all_goals try omega
  all_goals try simp

@[spec] theorem findIntegratedIndexV2_ok_le_size
    (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) :
    ⦃⌜(-1 : Int) ≤ leftIdx ∧ leftIdx < arr.size ∧ rightIdx ≤ arr.size⌝⦄
      findIntegratedIndexV2 leftIdx rightIdx input arr
    ⦃post⟨fun destIdx => ⌜destIdx ≤ arr.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [findIntegratedIndexV2, findRefIdx_spec, getElemExcept_spec]
  case inv1 =>
    exact post⟨fun ⟨xs, st⟩ => ⌜st.fst ≤ arr.size⌝, fun _ => ⌜True⌝⟩
  all_goals mleave
  case vc1.step =>
    omega
  all_goals try omega
  case vc11.step.except.handle =>
    intro
    trivial

@[spec] theorem integrateV2Item_spec
    (input : IntegrateInput A) (arr : Array (YjsItem A)) :
    ⦃⌜True⌝⦄ integrateV2Item input arr
    ⦃post⟨fun out => ⌜out.1 ≤ arr.size ∧ out.2.id = input.id⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [integrateV2Item, findLeftIdx_spec, findRightIdx_spec,
    findIntegratedIndexV2_ok_le_size, mkItemV2ByIndex_spec]
  all_goals mleave
  all_goals try omega
  all_goals try simp
