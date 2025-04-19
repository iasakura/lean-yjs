import LeanYjs.ActorId

variable (A : Type) [BEq A]

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr

inductive YjsItem : Type where
| item (origin : YjsPtr) (rightOrigin : YjsPtr) : ActorId -> A -> YjsItem
end

def YjsItem.origin {A : Type} (item : YjsItem A) : YjsPtr A :=
  match item with
  | YjsItem.item origin _ _ _ => origin

def YjsItem.rightOrigin {A : Type} (item : YjsItem A) : YjsPtr A :=
  match item with
  | YjsItem.item _ rightOrigin _ _ => rightOrigin

mutual
def YjsPtr.size {A : Type} (x : YjsPtr A) :=
  match x with
  | YjsPtr.itemPtr item => item.size + 1
  | YjsPtr.first => 0
  | YjsPtr.last => 0

def YjsItem.size {A : Type} (item : YjsItem A) :=
  match item with
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
