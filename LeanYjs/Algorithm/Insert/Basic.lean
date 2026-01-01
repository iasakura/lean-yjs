import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Algorithm.Basic

variable {A: Type} [DecidableEq A]

structure IntegrateInput (A : Type) where
  originId : Option YjsId
  rightOriginId : Option YjsId
  content : A
  id : YjsId

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

  return YjsItem.mk originPtr rightOriginPtr input.id input.content false

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
    match arr.findFinIdx? (fun item => item.id = id) with
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
  return YjsItem.mk (← getPtrExcept arr leftIdx) (← getPtrExcept arr rightIdx) input.id input.content false

def integrate (newItem : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findLeftIdx newItem.originId arr
  let rightIdx <- findRightIdx newItem.rightOriginId arr
  let destIdx <- findIntegratedIndex leftIdx rightIdx newItem arr

  let newItem := ← mkItemByIndex leftIdx rightIdx newItem arr
  return arr.insertIdxIfInBounds (Int.toNat destIdx) newItem

def isClockSafe (newItem : IntegrateInput A) (arr : Array (YjsItem A)) : Bool :=
  arr.all (fun item => item.id.clientId = newItem.id.clientId → newItem.id.clock > item.id.clock)

def integrateSafe (newItem : IntegrateInput A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  if isClockSafe newItem arr then
    integrate newItem arr
  else
    Except.error IntegrateError.error

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
