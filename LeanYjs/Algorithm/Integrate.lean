import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder

inductive IntegrateError where
| notFound : IntegrateError

variable {A: Type} [DecidableEq A]

def findPtrIdx (p : YjsPtr A) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match p with
  | YjsPtr.itemPtr item =>
    match Array.findIdx? (fun i => i = item) arr with
    | some idx => return idx
    | none => Except.error IntegrateError.notFound
  | YjsPtr.first => return -1
  | YjsPtr.last => return Array.size arr

def getElemExcept (arr : Array (YjsItem A)) (idx : Nat) : Except IntegrateError (YjsItem A) :=
  match arr[idx]? with
  | some item => return item
  | none => Except.error IntegrateError.notFound

def findIntegratedIndex (leftIdx rightIdx : Int) (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError Nat := do
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

def integrate (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findPtrIdx (YjsItem.origin newItem) arr
  let rightIdx <- findPtrIdx (YjsItem.rightOrigin newItem) arr

  let destIdx <- findIntegratedIndex leftIdx rightIdx newItem arr

  return (arr.insertIdxIfInBounds (Int.toNat destIdx) newItem)

def isClockSafe (newItem : YjsItem A) (arr : Array (YjsItem A)) : Bool :=
  arr.all (fun item => item.id.clientId = newItem.id.clientId → newItem.id.clock > item.id.clock)

def integrateSafe (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  if isClockSafe newItem arr then
    integrate newItem arr
  else
    Except.error IntegrateError.notFound

section Test

def init : Array (YjsItem String)  := #[]
def i1 := YjsItem.item (YjsPtr.first) (YjsPtr.last) (YjsId.mk 0 0) "0"
def i2 := YjsItem.item (YjsPtr.first) (YjsPtr.last) (YjsId.mk 0 1) "1"

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
