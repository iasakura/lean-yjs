import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Algorithm.Basic
import Std.Tactic.Do

variable {A: Type} [DecidableEq A]

structure IntegrateInput (A : Type) where
  originId : Option YjsId
  rightOriginId : Option YjsId
  content : A
  id : YjsId
deriving Repr, DecidableEq

def IntegrateInput.toItem (input : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError (YjsItem A) := do
  let originPtr <- match input.originId with
    | some id =>
      match arr.find? (fun item => item.id = id) with
      | some item => Except.ok (YjsPtr.itemPtr item)
      | none => Except.error IntegrateError.error
    | none => Except.ok YjsPtr.first

  let rightOriginPtr <- match input.rightOriginId with
    | some id =>
      match arr.find? (fun item => item.id = id) with
      | some item => Except.ok (YjsPtr.itemPtr item)
      | none => Except.error IntegrateError.error
    | none => Except.ok YjsPtr.last

  return YjsItem.mk originPtr rightOriginPtr input.id input.content

def findPtrIdx (p : YjsPtr A) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match p with
  | YjsPtr.itemPtr item =>
    match Array.findIdx? (fun i => i = item) arr with
    | some idx => return idx
    | none => Except.error IntegrateError.error
  | YjsPtr.first => return -1
  | YjsPtr.last => return Array.size arr

def getElemExcept (arr : Array (YjsItem A)) (idx : Nat) : Except IntegrateError (YjsItem A) :=
  match arr[idx]? with
  | some item => return item
  | none => Except.error IntegrateError.error

def findIntegratedIndex (leftIdx rightIdx : Int) (newItem : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError Nat := do
  let mut scanning := false
  let mut destIdx := leftIdx + 1
  for offset in [1:(rightIdx-leftIdx).toNat] do
    let i := (leftIdx + offset).toNat
    let other <- getElemExcept arr i

    let oLeftIdx <- findPtrIdx other.origin arr
    let oRightIdx <- findPtrIdx other.rightOrigin arr

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

  return (Int.toNat destIdx)

def findLeftIdx (originId : Option YjsId) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match originId with
  | some id =>
    match arr.findIdx? (fun item => item.id = id) with
    | some idx => return idx
    | none => Except.error IntegrateError.error
  | none => return -1

def findRightIdx (rightOriginId : Option YjsId) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match rightOriginId with
  | some id =>
    match arr.findIdx? (fun item => item.id = id) with
    | some idx => return idx
    | none => Except.error IntegrateError.error
  | none => return arr.size

def getPtrExcept (arr : Array (YjsItem A)) (idx : ℤ) : Except IntegrateError (YjsPtr A) :=
  if idx = -1 then
    Except.ok YjsPtr.first
  else if idx = arr.size then
    Except.ok YjsPtr.last
  else
    match arr[idx.toNat]? with
    | some item => Except.ok (YjsPtr.itemPtr item)
    | none => Except.error IntegrateError.error

def mkItemByIndex (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError (YjsItem A) := do
  return YjsItem.mk (← getPtrExcept arr leftIdx) (← getPtrExcept arr rightIdx) input.id input.content

def integrate (newItem : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findLeftIdx newItem.originId arr
  let rightIdx <- findRightIdx newItem.rightOriginId arr
  let destIdx <- findIntegratedIndex leftIdx rightIdx newItem arr

  let newItem := ← mkItemByIndex leftIdx rightIdx newItem arr
  return arr.insertIdxIfInBounds (Int.toNat destIdx) newItem

def isClockSafe (id : YjsId) (arr : Array (YjsItem A)) : Bool :=
  arr.all (fun item => item.id.clientId = id.clientId → id.clock > item.id.clock)

def integrateSafe (newItem : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  if isClockSafe newItem.id arr then
    integrate newItem arr
  else
    Except.error IntegrateError.error

def YjsState.insert (arr : YjsState A) (input : IntegrateInput A) : Except IntegrateError (YjsState A) := do
  let newArr <- integrateSafe input arr.items
  return { arr with items := newArr }

open Std.Do

theorem except_bind_eq_ok_exists {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β} :
    x >>= f = Except.ok y →
    ∃ a, x = Except.ok a ∧ f a = Except.ok y := by
  intro h
  cases x with
  | error err =>
    cases h
  | ok a =>
    exact ⟨ a, rfl, h ⟩

@[spec] theorem findPtrIdx_spec (p : YjsPtr A) (arr : Array (YjsItem A)) :
    ⦃⌜True⌝⦄ findPtrIdx p arr ⦃post⟨fun idx => ⌜(-1 : Int) ≤ idx ∧ idx ≤ arr.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [findPtrIdx]
  all_goals mleave
  case vc1.h_1.h_1 =>
    rename_i _ h_find
    rw [Array.findIdx?_eq_some_iff_getElem] at h_find
    obtain ⟨ h_lt, _, _ ⟩ := h_find
    omega
  case vc3.h_2 =>
    constructor
    · omega
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast (Nat.zero_le arr.size)
      omega
  case vc4.h_3 =>
    constructor
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast (Nat.zero_le arr.size)
      omega
    · omega

@[spec] theorem getElemExcept_spec (arr : Array (YjsItem A)) (idx : Nat) :
    ⦃⌜True⌝⦄ getElemExcept arr idx
    ⦃post⟨fun _ => ⌜idx < arr.size⌝, fun _ => ⌜arr.size ≤ idx⌝⟩⦄ := by
  mvcgen [getElemExcept]
  all_goals mleave
  case vc1.h_1 =>
    rename_i item h_some
    obtain ⟨h_lt, _⟩ := (Array.getElem?_eq_some_iff.mp h_some)
    exact h_lt
  case vc2.h_2 =>
    rename_i h_none
    simp [wp]
    simpa [Array.getElem?_eq_none_iff] using h_none

@[spec] theorem findLeftIdx_spec (originId : Option YjsId) (arr : Array (YjsItem A)) :
    ⦃⌜True⌝⦄ findLeftIdx originId arr
    ⦃post⟨fun leftIdx => ⌜(-1 : Int) ≤ leftIdx ∧ leftIdx < arr.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [findLeftIdx]
  all_goals mleave
  case vc1.h_1.h_1 =>
    rename_i _ h_find
    rw [Array.findIdx?_eq_some_iff_getElem] at h_find
    obtain ⟨ h_lt, _, _ ⟩ := h_find
    constructor
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast (Nat.zero_le arr.size)
      omega
    · exact_mod_cast h_lt
  case vc3.h_2 =>
    constructor
    · omega
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast (Nat.zero_le arr.size)
      omega

@[spec] theorem findRightIdx_spec (rightOriginId : Option YjsId) (arr : Array (YjsItem A)) :
    ⦃⌜True⌝⦄ findRightIdx rightOriginId arr
    ⦃post⟨fun rightIdx => ⌜(-1 : Int) ≤ rightIdx ∧ rightIdx ≤ arr.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [findRightIdx]
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
    · have h_nonneg : (0 : Int) ≤ arr.size := by exact_mod_cast (Nat.zero_le arr.size)
      omega
    · omega

@[spec] theorem getPtrExcept_spec (arr : Array (YjsItem A)) (idx : Int) :
    ⦃⌜(-1 : Int) ≤ idx ∧ idx ≤ arr.size⌝⦄ getPtrExcept arr idx
    ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [getPtrExcept]
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

@[spec] theorem mkItemByIndex_spec
  (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) :
    ⦃⌜(-1 : Int) ≤ leftIdx ∧ leftIdx ≤ arr.size ∧ (-1 : Int) ≤ rightIdx ∧ rightIdx ≤ arr.size⌝⦄
      mkItemByIndex leftIdx rightIdx input arr
    ⦃post⟨fun item => ⌜item.id = input.id⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [mkItemByIndex, getPtrExcept_spec]
  all_goals mleave
  all_goals try omega
  all_goals try simp

@[spec] theorem findIntegratedIndex_ok_le_size
  (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) :
  ⦃⌜(-1 : Int) ≤ leftIdx ∧ leftIdx < arr.size ∧ rightIdx ≤ arr.size⌝⦄
    findIntegratedIndex leftIdx rightIdx input arr
  ⦃post⟨fun destIdx => ⌜destIdx ≤ arr.size⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [findIntegratedIndex, findPtrIdx_spec, getElemExcept_spec]
  case inv1 =>
    exact post⟨fun ⟨xs, st⟩ => ⌜st.fst ≤ arr.size⌝, fun _ => ⌜True⌝⟩
  all_goals mleave
  case vc1.step =>
    omega
  all_goals try omega
  case vc11.step.except.handle =>
    intro
    trivial

theorem findIntegratedIndex_ok_le_size_from_eq
  (leftIdx rightIdx : Int) (input : IntegrateInput A) (arr : Array (YjsItem A)) (destIdx : Nat) :
  (-1 : Int) ≤ leftIdx →
  leftIdx < arr.size →
  rightIdx ≤ arr.size →
  findIntegratedIndex leftIdx rightIdx input arr = Except.ok destIdx →
  destIdx ≤ arr.size := by
  intro h_left_ge h_left_lt h_right_le h_ok
  have hP :
      (match findIntegratedIndex leftIdx rightIdx input arr with
      | Except.ok d => d ≤ arr.size
      | Except.error _ => True) := by
    apply (Except.of_wp (prog := findIntegratedIndex leftIdx rightIdx input arr)
      (P := fun r => match r with
        | Except.ok d => d ≤ arr.size
        | Except.error _ => True))
    mvcgen [findIntegratedIndex, findPtrIdx_spec, getElemExcept_spec]
  simpa [h_ok] using hP

theorem insert_ok_exists_insertIdx
  (s s' : YjsState A) (input : IntegrateInput A) :
  s.insert input = Except.ok s' →
  ∃ i, ∃ h : i ≤ s.items.size, ∃ item, s' = { s with items := s.items.insertIdx i item h } := by
  intro h_insert
  have hP :
      (match s.insert input with
      | Except.ok st => ∃ i, ∃ h : i ≤ s.items.size, ∃ item, st = { s with items := s.items.insertIdx i item h }
      | Except.error _ => True) := by
    apply (Except.of_wp (prog := s.insert input)
      (P := fun r => match r with
        | Except.ok st => ∃ i, ∃ h : i ≤ s.items.size, ∃ item, st = { s with items := s.items.insertIdx i item h }
        | Except.error _ => True))
    mvcgen [YjsState.insert, integrateSafe, integrate, findLeftIdx_spec, findRightIdx_spec, findIntegratedIndex_ok_le_size, mkItemByIndex_spec]
    all_goals mleave
    all_goals try omega
    all_goals try grind
    case vc3.isTrue.success.success.post.success.post.success =>
      rename_i destIdx h_dest_le item _
      refine ⟨ destIdx, h_dest_le, item, ?_ ⟩
      simp [Array.insertIdxIfInBounds, h_dest_le]
  simpa [h_insert] using hP

section Test

def init : Array (YjsItem String)  := #[]
def i1 := IntegrateInput.mk none none "0" (YjsId.mk 0 0)
def i2 := IntegrateInput.mk none none "1" (YjsId.mk 0 1)

def test12 := do
  let arr1 <- integrate i1 init
  integrate i2 arr1

def test21 := do
  let arr1 <- integrate i2 init
  integrate i1 arr1

#eval match test12 with
| Except.ok arr => IO.println $ arr.map (fun item => YjsItem.content item)
| Except.error _err => IO.println s!"Error"

#eval match test21 with
| Except.ok arr => IO.println $ arr.map (fun item => YjsItem.content item)
| Except.error _err => IO.println s!"Error"

end Test

section InconsistencyExample

/--
This example shows that the insert algorithm can produce different results depending on the order of integration, which can lead to inconsistency if not handled properly. In this example, we have two items "o" and "n" that are both inserted after "a" and "b". Depending on the order of integration, "o" can end up before "n" or vice versa, which is inconsistent with the intention of the operations.
This is because o doesn't satisfy the condition origin_nearest_reachable in ItemSetInvariant.lean:
∀ (o r : YjsPtr A) c id x,
    P (YjsItem.mk o r id c) ->
    OriginReachable (A := A) (YjsItem.mk o r id c) x ->
    (YjsLeq' x o) ∨ (YjsLeq' r x)
This condition means that for any item, if there is another item that is reachable from it through the origin or right origin pointers, then that item must be either less than or equal to the original item or greater than or equal to the right origin. In this example, "a" is reachable from "o" through the origin pointer, but "o"'s origin and rightOrigin are none (= YjsPtr.first) and "b" respectively. Because YjsPtr.first < "a" < "b", origin_nearest_reachable is not satisfied for "o".
For this reason, the Yjs insert algorithm cannot satisfy the "concurrent commutativity" property, because it requires that insert is commutative beginning from any state, but origin_nearest_reachable is not hold for any state (the state after inserting "a" and "b" doesn't satisfy origin_nearest_reachable for "o"). To fix this issue, we give an stronger version of concurrent commutativity. See Network/StrongCausalOrder.lean .
-/

def a := IntegrateInput.mk none none "a" (YjsId.mk 0 0)
def b := IntegrateInput.mk (YjsId.mk 0 0) none "b" (YjsId.mk 1 0)
def o := IntegrateInput.mk none (YjsId.mk 1 0) "o" (YjsId.mk 2 0)
def n := IntegrateInput.mk (YjsId.mk 0 0) none "n" (YjsId.mk 3 0)

def inconsistent1 := do
  let mut arr := YjsState.empty
  arr ← arr.insert a
  arr ← arr.insert b
  arr ← arr.insert o
  arr ← arr.insert n
  return arr

def inconsistent2 := do
  let mut arr := YjsState.empty
  arr ← arr.insert a
  arr ← arr.insert b
  arr ← arr.insert n
  arr ← arr.insert o
  return arr

#eval match inconsistent1 with
| Except.ok arr => IO.println $ arr.items.map (fun item => YjsItem.content item)
| Except.error _err => IO.println s!"Error"

#eval match inconsistent2 with
| Except.ok arr => IO.println $ arr.items.map (fun item => YjsItem.content item)
| Except.error _err => IO.println s!"Error"

end InconsistencyExample
