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

inductive LoopCommand (A : Type) where
| Continue : A -> LoopCommand A
| Break : A -> LoopCommand A

def fold_range {M : Type -> Type} [Monad M] {A : Type} (a b : Nat) (f : A → Nat → M (LoopCommand (M A))) (acc : M A) : M A := do
  if a ≥ b then acc
  else
    let acc <- acc
    let cmd <- f acc a
    match cmd with
    | LoopCommand.Continue acc => fold_range (a + 1) b f acc
    | LoopCommand.Break acc => acc
  termination_by (b - a)

def integrate (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findIdx (YjsItem.origin newItem) arr
  let rightIdx <- findIdx (YjsItem.rightOrigin newItem) arr
  let (_, i) <- fold_range (Int.toNat (leftIdx + 1)) (Int.toNat rightIdx) (acc := Except.ok (false, leftIdx + 1)) (fun acc i => do
    let (scanning, leftIdx) := acc
    let oItem <- getExcept arr i
    let oLeftIdx <- findIdx oItem.origin arr
    let oRightIdx <- findIdx oItem.rightOrigin arr
    if oLeftIdx < leftIdx then
      return LoopCommand.Break (return (true, i))
    else if oLeftIdx == leftIdx then
      if decide (YjsItem.id newItem > YjsItem.id oItem) then
        return (LoopCommand.Continue (return (false, i + 1)))
      else if oRightIdx == rightIdx then
        return (LoopCommand.Break (return (false, i + 1)))
      else
        return (LoopCommand.Continue (return (true, i + 1)))
    else
      return ((LoopCommand.Continue (return (scanning, i + 1)))))
  return (Array.insertIdxIfInBounds arr (Int.toNat i) newItem)

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
