import LeanYjs.Indirect.Algorithm.Basic
import LeanYjs.Algorithm.Insert.Basic

namespace Indirect

variable {A : Type} [DecidableEq A]

def findRefIdx (p : YjsRef) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match p with
  | YjsRef.itemId id =>
    match Array.findIdx? (fun i => i.id = id) arr with
    | some idx => return idx
    | none => Except.error IntegrateError.error
  | YjsRef.first => return -1
  | YjsRef.last => return Array.size arr

def getElemExcept (arr : Array (YjsItem A)) (idx : Nat) : Except IntegrateError (YjsItem A) :=
  match arr[idx]? with
  | some item => return item
  | none => Except.error IntegrateError.error

/-- The set-based scan of `_root_.findIntegratedIndex`, on id-referencing items. -/
def findIntegratedIndex (leftIdx rightIdx : Int) (newItem : IntegrateInput A)
    (arr : Array (YjsItem A)) : Except IntegrateError Nat := do
  let mut destIdx := leftIdx + 1
  let mut itemsBeforeOrigin : List YjsId := []
  let mut conflictingItems : List YjsId := []
  for offset in [1:(rightIdx-leftIdx).toNat] do
    let i := (leftIdx + offset).toNat
    let other <- getElemExcept arr i
    itemsBeforeOrigin := other.id :: itemsBeforeOrigin
    conflictingItems := other.id :: conflictingItems

    if other.origin.id? = newItem.originId then
      if other.id.clientId < newItem.id.clientId then
        destIdx := i + 1
        conflictingItems := []
      else if other.rightOrigin.id? = newItem.rightOriginId then
        break
    else if idMem other.origin.id? itemsBeforeOrigin then
      if !idMem other.origin.id? conflictingItems then
        destIdx := i + 1
        conflictingItems := []
    else
      break

  return destIdx.toNat

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

def mkItem (input : IntegrateInput A) : YjsItem A where
  origin := YjsRef.ofOriginId input.originId
  rightOrigin := YjsRef.ofRightOriginId input.rightOriginId
  id := input.id
  content := input.content

def integrate (newItem : IntegrateInput A) (arr : Array (YjsItem A)) :
    Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findLeftIdx newItem.originId arr
  let rightIdx <- findRightIdx newItem.rightOriginId arr
  let destIdx <- findIntegratedIndex leftIdx rightIdx newItem arr
  return arr.insertIdxIfInBounds (Int.toNat destIdx) (mkItem newItem)

def isClockSafe (id : YjsId) (arr : Array (YjsItem A)) : Bool :=
  arr.all (fun item => item.id.clientId = id.clientId → id.clock > item.id.clock)

def integrateSafe (newItem : IntegrateInput A) (arr : Array (YjsItem A)) :
    Except IntegrateError (Array (YjsItem A)) := do
  if isClockSafe newItem.id arr then
    integrate newItem arr
  else
    Except.error IntegrateError.error

def YjsState.insert (arr : YjsState A) (input : IntegrateInput A) :
    Except IntegrateError (YjsState A) := do
  let newArr <- integrateSafe input arr.items
  return { arr with items := newArr }

end Indirect
