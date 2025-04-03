-- This module serves as the root of the `LeanYjs` library.
-- Import modules here that should be built as part of the library.
import LeanYjs.Basic
import Mathlib.Order.Defs.Unbundled

variable (A : Type) [BEq A]

def ActorId := Nat

instance : LT ActorId where
  lt x y := Nat.lt x y

instance : DecidableRel (· < · : ActorId → ActorId → Prop) := by
  intros x y
  unfold ActorId at x y
  apply (inferInstance : Decidable (x < y))

instance ActorIdOfNat n : OfNat ActorId n where
  ofNat := n

mutual
inductive YjsPtr : Type where
| itemPtr : YjsItem -> YjsPtr
| first : YjsPtr
| last : YjsPtr

inductive YjsItem : Type where
| item : (origin : YjsPtr) -> (rightOrigin : YjsPtr) -> ActorId -> A -> YjsItem
end

instance : BEq ActorId where
  beq x y := by
    unfold ActorId at x y
    apply Nat.beq x y

mutual
def yjsItemEq (x y : YjsItem A) : Bool :=
  match x, y with
  | YjsItem.item origin1 rightOrigin1 id1 c1, YjsItem.item origin2 rightOrigin2 id2 c2 =>
    yjsPtrEq origin1 origin2 && yjsPtrEq rightOrigin1 rightOrigin2 && id1 == id2 && c1 == c2

def yjsPtrEq (x y : YjsPtr A) : Bool :=
  match x, y with
  | YjsPtr.itemPtr item1, YjsPtr.itemPtr item2 => yjsItemEq item1 item2
  | YjsPtr.first, YjsPtr.first => true
  | YjsPtr.last, YjsPtr.last => true
  | _, _ => false
end

instance BEqYjsItem : BEq (YjsItem A) where
  beq := yjsItemEq _

instance BEqYjsPtr : BEq (@YjsPtr A) where
  beq := yjsPtrEq _

instance : Coe (YjsItem A) (YjsPtr A) where
  coe item := YjsPtr.itemPtr item

def YjsItem.origin {A : Type} : YjsItem A -> YjsPtr A
| YjsItem.item origin _  _ _ => origin

def YjsItem.rightOrigin {A : Type} : YjsItem A -> YjsPtr A
| YjsItem.item _ rightOrigin _ _ => rightOrigin

def YjsItem.id {A : Type} : YjsItem A -> ActorId
| YjsItem.item _ _ id _ => id

-- inductive YjsLessThan1 (A : Type) : YjsItem A -> YjsItem A -> Prop where
-- | ltOrigin : forall (item : YjsItem A) (right : YjsPtr A) (id : ActorId) (c : A),
--     YjsLessThan1 A item (YjsItem.item (YjsPtr.itemPtr item) right id c)
-- | ltRightOrigin : forall (item : YjsItem A) (left : YjsPtr A) (id : ActorId) (c : A),
--     YjsLessThan1 A (YjsItem.item left (YjsPtr.itemPtr item) id c) item

-- /- transitive closure -/
-- inductive YjsLessThanTr {a : Type} : YjsItem a -> YjsItem a -> Prop where
-- | base : forall (item1 item2 : YjsItem a), YjsLessThan1 a item1 item2 -> YjsLessThanTr item1 item2
-- | trans : forall (item1 item2 item3 : YjsItem a), YjsLessThanTr item1 item2 -> YjsLessThan1 a item2 item3 -> YjsLessThanTr item1 item3

inductive YjsLessThan {A : Type} : YjsPtr A -> YjsPtr A -> Prop where
| ltFirst: forall l r id (c : A), YjsLessThan (YjsPtr.first) (YjsItem.item l r id c)
| ltLast: forall l r id (c : A), YjsLessThan (YjsItem.item l r id c) (YjsPtr.last)
| ltL1 : forall l r id c, YjsLessThan l (YjsItem.item l r id c)
| ltR1 : forall l r id c, YjsLessThan (YjsItem.item l r id c) r
| ltL2 : forall l1 r1 id1 l2 r2 id2 (c1 c2 : A),
  YjsLessThan (YjsItem.item l1 r1 id1 c1) l2 -> YjsLessThan (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
| ltR2 : forall l1 r1 id1 l2 r2 id2 (c1 c2 : A),
  YjsLessThan r1 (YjsItem.item l2 r2 id2 c2) -> YjsLessThan (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
| ltOriginDiff : forall l1 l2 (r1 r2 : YjsItem A) id1 id2 c1 c2,
  YjsLessThan l2 l1
  -> YjsLessThan (YjsItem.item l1 r1 id1 c1) r2
  -> YjsLessThan l1 (YjsItem.item l2 r2 id2 c2)
  -> YjsLessThan (YjsItem.item l2 r2 id2 c2) r1
  -> YjsLessThan (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
| ltOriginSame : forall l r1 r2 id1 id2 (c1 c2 : A),
  YjsLessThan (YjsItem.item l r1 id1 c1) r2
  -> YjsLessThan (YjsItem.item l r2 id2 c2) r1
  -> id1 < id2
  -> YjsLessThan (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2)

namespace ex1
  open Nat
  def item1 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 1 1
  def item2 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 2 2

  example : YjsLessThan item1 item2 :=
  by
    unfold item1 item2
    apply YjsLessThan.ltOriginSame <;> try rfl
    . apply YjsLessThan.ltLast
    . apply YjsLessThan.ltLast
    simp [ActorId]
end ex1

namespace ex2
  def item0 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 0 0
  def item1 : YjsPtr Nat := YjsItem.item YjsPtr.first YjsPtr.last 1 1
  def item2 : YjsPtr Nat := YjsItem.item YjsPtr.first item0 2 2

  example : YjsLessThan item2 item1 :=
  by
    apply YjsLessThan.ltR2
    . apply YjsLessThan.ltOriginSame
      apply YjsLessThan.ltLast
      apply YjsLessThan.ltLast
      simp [ActorId]
end ex2

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

theorem integrate_sound (A: Type) [BEq A] (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  ArrayPairwise (fun (x y : YjsItem A) => @YjsLessThan A x y) arr
  -> integrate newItem arr = Except.ok newArr
  -> ArrayPairwise (fun (x y : YjsItem A) => @YjsLessThan A x y) newArr := by
  sorry

theorem order_is_strict_total: IsStrictTotalOrder _ (@YjsLessThan A) := by
  sorry

theorem integrate_commutative (A: Type) [BEq A] (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
  sorry
