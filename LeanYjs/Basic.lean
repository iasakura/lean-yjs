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

theorem order_is_strict_total: IsStrictTotalOrder _ (@YjsLessThan A) := by
  sorry
