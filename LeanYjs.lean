-- This module serves as the root of the `LeanYjs` library.
-- Import modules here that should be built as part of the library.
import LeanYjs.Basic

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

inductive YjsLessThan1 (A : Type) : YjsItem A -> YjsItem A -> Prop where
| ltOrigin : forall (item : YjsItem A) (right : YjsPtr A) (id : ActorId) (c : A),
    YjsLessThan1 A item (YjsItem.item (YjsPtr.itemPtr item) right id c)
| ltRightOrigin : forall (item : YjsItem A) (left : YjsPtr A) (id : ActorId) (c : A),
    YjsLessThan1 A (YjsItem.item left (YjsPtr.itemPtr item) id c) item

/- transitive closure -/
inductive YjsLessThanTr {a : Type} : YjsItem a -> YjsItem a -> Prop where
| base : forall (item1 item2 : YjsItem a), YjsLessThan1 a item1 item2 -> YjsLessThanTr item1 item2
| trans : forall (item1 item2 item3 : YjsItem a), YjsLessThanTr item1 item2 -> YjsLessThan1 a item2 item3 -> YjsLessThanTr item1 item3

inductive YjsLessThan {A : Type} : YjsItem A -> YjsItem A -> Prop where
| ltOrigin : forall item1 item2, YjsLessThanTr item1 item2 -> YjsLessThan item1 item2
| ltTr : forall item1 item2 item3, YjsLessThan item1 item2 -> YjsLessThan item2 item3 -> YjsLessThan item1 item3
| lt1 : forall (left1 left2 right1 right2 : YjsItem A) (id1 id2 : ActorId) (c1 c2 : A),
    item1 = YjsItem.item left1 right1 id1 c1
    -> item2 = YjsItem.item left2 right2 id2 c2
    /- left1 < item2 < right1 -/
    -> YjsLessThanTr left1 item2 -> YjsLessThanTr item2 right1
    /- left1 < left2 -/
    -> YjsLessThanTr left1 left2
    /- left2 < item1 -/
    -> YjsLessThan left2 item1
    -> YjsLessThan item2 item1
| lt2 : forall (left1 left2 right1 right2 : YjsItem A) (id1 id2 : ActorId) (c1 c2 : A),
    item1 = YjsItem.item left1 right1 id1 c1
    -> item2 = YjsItem.item left2 right2 id2 c2
    /- left1 < item2 < right1 -/
    -> YjsLessThanTr left1 item2 -> YjsLessThanTr item2 right1
    /- left2 < left1 -/
    -> YjsLessThanTr left2 left1
    -> YjsLessThan item1 item2
| ltId1 : forall (left right1 right2 : YjsItem A) (id1 id2 : ActorId) (c1 c2 : A),
    item1 = YjsItem.item left right1 id1 c1
    -> item2 = YjsItem.item left right2 id2 c2
    -> YjsLessThan item1 right2
    -> id1 < id2
    -> YjsLessThan item1 item2
| ltId2 : forall (left right : YjsPtr A) (id1 id2 : ActorId) (c1 c2 : A),
    item1 = YjsItem.item left right id1 c1
    -> item2 = YjsItem.item left right id2 c2
    -> id1 < id2
    -> YjsLessThan item1 item2
| ltId3 : forall (left : YjsPtr A) (right1 right2 : YjsItem A) (id1 id2 : ActorId) (c1 c2 : A),
    item1 = YjsItem.item left right1 id1 c1
    -> item2 = YjsItem.item left right2 id2 c2
    -> id1 < id2
    /- left < item2 < right1 -/
    -> YjsLessThan item2 right1
    -> YjsLessThan item1 right2
    -> YjsLessThan item1 item2

namespace ex1
  open Nat
  def item1 := YjsItem.item YjsPtr.first YjsPtr.last 1 1
  def item2 := YjsItem.item YjsPtr.first YjsPtr.last 2 2

  example : YjsLessThan item1 item2 :=
  by
    apply @YjsLessThan.ltId2 (item1 := item1) (item2 := item2) <;> try rfl
    simp [ActorId]
end ex1

namespace ex2
  def item0 := YjsItem.item YjsPtr.first YjsPtr.last 0 0
  def item1 := YjsItem.item YjsPtr.first YjsPtr.last 1 1
  def item2 := YjsItem.item YjsPtr.first item0 2 2

  example : YjsLessThan item2 item1 :=
  by
    apply YjsLessThan.ltTr (item2 := item0)
    . apply YjsLessThan.ltOrigin
      apply YjsLessThanTr.base
      apply YjsLessThan1.ltRightOrigin
    . apply YjsLessThan.ltId2 <;> try rfl
      unfold ActorId
      decide
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
  match Array.get? arr idx with
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
  ArrayPairwise (@YjsLessThan A) arr
  -> integrate newItem arr = Except.ok newArr
  -> ArrayPairwise (@YjsLessThan A) newArr := by
  sorry
