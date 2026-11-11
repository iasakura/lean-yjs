import LeanYjs.Item

namespace Indirect

inductive YjsRef where
  | itemId (id : YjsId)
  | first
  | last
  deriving Repr, DecidableEq

def YjsRef.ofDirectPtr {A : Type} : _root_.YjsPtr A → YjsRef
  | .itemPtr item => .itemId item.id
  | .first => .first
  | .last => .last

/-- The id a reference refers to: `none` for the sentinels `first` and `last`. -/
@[simp] def YjsRef.id? : YjsRef → Option YjsId
  | .itemId id => some id
  | .first => none
  | .last => none

def YjsRef.ofOriginId : Option YjsId → YjsRef
  | some id => .itemId id
  | none => .first

def YjsRef.ofRightOriginId : Option YjsId → YjsRef
  | some id => .itemId id
  | none => .last

structure YjsItem (A : Type) where
  origin : YjsRef
  rightOrigin : YjsRef
  id : YjsId
  content : A
deriving Repr, DecidableEq

def ofDirectItem {A : Type} (item : _root_.YjsItem A) : YjsItem A where
  origin := YjsRef.ofDirectPtr item.origin
  rightOrigin := YjsRef.ofDirectPtr item.rightOrigin
  id := item.id
  content := item.content

end Indirect
