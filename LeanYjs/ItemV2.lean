import LeanYjs.Item

variable (A : Type)

inductive ItemRef where
  | first
  | last
  | idRef (id : YjsId)
deriving Repr, DecidableEq

structure YjsItemV2 : Type where
  origin : ItemRef
  rightOrigin : ItemRef
  id : YjsId
  content : A
deriving Repr, DecidableEq

namespace ItemRef

def toOptionId : ItemRef -> Option YjsId
  | .first => none
  | .last => none
  | .idRef id => some id

def isSentinel : ItemRef -> Prop
  | .first => True
  | .last => True
  | .idRef _ => False

@[simp] theorem toOptionId_first :
    ItemRef.toOptionId ItemRef.first = none := rfl

@[simp] theorem toOptionId_last :
    ItemRef.toOptionId ItemRef.last = none := rfl

@[simp] theorem toOptionId_idRef (id : YjsId) :
    ItemRef.toOptionId (.idRef id) = some id := rfl

@[simp] theorem isSentinel_first :
    ItemRef.isSentinel ItemRef.first := trivial

@[simp] theorem isSentinel_last :
    ItemRef.isSentinel ItemRef.last := trivial

@[simp] theorem not_isSentinel_idRef (id : YjsId) :
    ¬ ItemRef.isSentinel (.idRef id) := by
  simp [ItemRef.isSentinel]

end ItemRef

namespace YjsItemV2

def toRef (item : YjsItemV2 A) : ItemRef :=
  .idRef item.id

@[simp] theorem toRef_id (item : YjsItemV2 A) :
    item.toRef = .idRef item.id := rfl

end YjsItemV2
