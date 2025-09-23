import LeanYjs.ClientId

variable (A : Type) [DecidableEq A]

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr
  deriving Repr, DecidableEq

inductive YjsItem : Type where
| item (origin : YjsPtr) (rightOrigin : YjsPtr) : ClientId -> A -> YjsItem
deriving Repr, DecidableEq
end

def YjsItem.origin {A : Type} : YjsItem A -> YjsPtr A
  | YjsItem.item origin _ _ _ => origin

def YjsItem.rightOrigin {A : Type} : YjsItem A -> YjsPtr A
  | YjsItem.item _ rightOrigin _ _ => rightOrigin

def YjsItem.content {A : Type} : YjsItem A -> A
  | YjsItem.item _ _ _ content => content

mutual
def YjsPtr.size {A : Type} : YjsPtr A -> Nat
  | YjsPtr.itemPtr item => item.size + 1
  | YjsPtr.first => 0
  | YjsPtr.last => 0

def YjsItem.size {A : Type} : YjsItem A -> Nat
  | YjsItem.item origin rightOrigin _ _ =>
    origin.size + rightOrigin.size + 2
end

instance : BEq ClientId where
  beq x y := by
    unfold ClientId at x y
    apply Nat.beq x y

instance : BEq (YjsItem A) where
  beq := fun x y => decide (x = y)

instance : BEq (@YjsPtr A) where
  beq := fun x y => decide (x = y)

instance : LawfulBEq (YjsItem A) := by
  constructor
  . intros x y
    simp

instance : Coe (YjsItem A) (YjsPtr A) where
  coe item := YjsPtr.itemPtr item

def YjsItem.id {A : Type} : YjsItem A -> ClientId
| YjsItem.item _ _ id _ => id

-- The theorem you requested: excluded middle for YjsItem equality
-- This follows from the law of excluded middle in classical logic
theorem yjsItem_decidable_eq (x y : YjsItem A) : x = y ∨ x ≠ y := by
  classical
  by_cases h : x = y
  · left; exact h
  · right; exact h
