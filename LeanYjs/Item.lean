import LeanYjs.ActorId

variable (A : Type) [BEq A] [LawfulBEq A]

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr
  deriving Repr, DecidableEq

inductive YjsItem : Type where
| item (origin : YjsPtr) (rightOrigin : YjsPtr) : ActorId -> A -> YjsItem
deriving Repr, DecidableEq
end

def YjsItem.origin {A : Type} : YjsItem A -> YjsPtr A
  | YjsItem.item origin _ _ _ => origin

def YjsItem.rightOrigin {A : Type} : YjsItem A -> YjsPtr A
  | YjsItem.item _ rightOrigin _ _ => rightOrigin

mutual
def YjsPtr.size {A : Type} : YjsPtr A -> Nat
  | YjsPtr.itemPtr item => item.size + 1
  | YjsPtr.first => 0
  | YjsPtr.last => 0

def YjsItem.size {A : Type} : YjsItem A -> Nat
  | YjsItem.item origin rightOrigin _ _ =>
    origin.size + rightOrigin.size + 2
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

def YjsItem.id {A : Type} : YjsItem A -> ActorId
| YjsItem.item _ _ id _ => id

-- The theorem you requested: excluded middle for YjsItem equality
-- This follows from the law of excluded middle in classical logic
omit [BEq A] in
theorem yjsItem_decidable_eq (x y : YjsItem A) : x = y ∨ x ≠ y := by
  classical
  by_cases h : x = y
  · left; exact h
  · right; exact h
