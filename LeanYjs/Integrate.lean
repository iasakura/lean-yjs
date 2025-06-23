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

inductive ArrayPairwise {α : Type} (f : α -> α -> Prop) : Array α -> Prop where
| empty : ArrayPairwise f #[] -- empty array is pairwise
| push : forall (a : α) (arr : Array α),
  ArrayPairwise f arr -> (forall b: α, b ∈ arr -> f b a)
  -> ArrayPairwise f (Array.push arr a) -- if the tail is pairwise, then adding an element is pairwise

theorem integrate_sound (A: Type) [BEq A] (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) h1 :
  ArrayPairwise (fun (x y : YjsItem A) => @YjsLt A h1 x y) arr
  -> integrate newItem arr = Except.ok newArr
  -> ∃ h2, ArrayPairwise (fun (x y : YjsItem A) => @YjsLt A h2 x y) newArr := by
  sorry

theorem integrate_commutative (A: Type) [BEq A] (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
