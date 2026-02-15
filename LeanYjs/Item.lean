import LeanYjs.ClientId

variable (A : Type) [DecidableEq A]

structure YjsId where
  clientId : ClientId
  clock : Nat
deriving Repr, DecidableEq

instance : LT YjsId where
  lt id1 id2 :=
    if id1.clientId == id2.clientId then
      id1.clock > id2.clock
    else
      id1.clientId < id2.clientId

instance : DecidableRel (· < · : YjsId → YjsId → Prop) := by
  intros x y
  obtain ⟨ x_clientId, x_clock ⟩ := x
  obtain ⟨ y_clientId, y_clock ⟩ := y
  simp only [LT.lt]
  simp
  split
  . by_cases h : x_clock > y_clock
    . exact isTrue h
    . apply isFalse; omega
  . by_cases h : x_clientId < y_clientId
    . exact isTrue h
    . apply isFalse; omega

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr
  deriving Repr, DecidableEq

structure YjsItem : Type where
  origin : YjsPtr
  rightOrigin : YjsPtr
  id : YjsId
  content : A
deriving Repr, DecidableEq
end

mutual
def YjsPtr.size {A : Type} : YjsPtr A -> Nat
  | YjsPtr.itemPtr item => item.size + 1
  | YjsPtr.first => 0
  | YjsPtr.last => 0

def YjsItem.size {A : Type} : YjsItem A -> Nat
  | YjsItem.mk origin rightOrigin _ _ =>
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
