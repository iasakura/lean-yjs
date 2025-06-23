import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder

inductive IntegrateError where
| notFound : IntegrateError

variable {A: Type} [BEq A]

def findIdx (p : YjsPtr A) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match p with
  | YjsPtr.itemPtr item =>
    match Array.findIdx? (fun i => i == item) arr with
    | some idx => return idx
    | none => Except.error IntegrateError.notFound
  | YjsPtr.first => return 0
  | YjsPtr.last => return (Array.size arr - 1)

def getExcept (arr : Array (YjsItem A)) (idx : Nat) : Except IntegrateError (YjsItem A) :=
  match arr[idx]? with
  | some item => return item
  | none => Except.error IntegrateError.notFound

def integrate (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findIdx (YjsItem.origin newItem) arr
  let rightIdx <- findIdx (YjsItem.rightOrigin newItem) arr
  let leftIdx := Int.toNat leftIdx
  let rightIdx := Int.toNat rightIdx

  let mut scanning := false
  let mut destIdx := leftIdx + 1
  for i in [leftIdx+1:rightIdx] do
    let other <- getExcept arr i

    if !scanning then
      destIdx := i

    let oLeftIdx <- findIdx other.origin arr
    let oRightIdx <- findIdx other.rightOrigin arr

    if oLeftIdx < leftIdx then
      break
    else if oLeftIdx == leftIdx then
      if newItem.id > other.id then
        scanning := false
        continue
      else if oRightIdx == rightIdx then
        break
      else
        scanning := true
        continue
    else
      continue

  return (Array.insertIdxIfInBounds arr (Int.toNat destIdx) newItem)
