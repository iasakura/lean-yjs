import LeanYjs.Indirect.Item
import LeanYjs.Algorithm.Basic

namespace Indirect

abbrev DeletedIdSet := _root_.DeletedIdSet

structure YjsState (A : Type) where
  items : Array (YjsItem A)
  deletedIds : DeletedIdSet

instance : Coe (YjsState A) (Array (YjsItem A)) where
  coe state := state.items

instance : Coe (Array (YjsItem A)) (YjsState A) where
  coe items := { items := items, deletedIds := ∅ }

@[simp] theorem coeArrayToState_items (items : Array (YjsItem A)) :
    ((items : YjsState A)).items = items := rfl

@[simp] theorem coeArrayToState_deletedIds (items : Array (YjsItem A)) :
    ((items : YjsState A)).deletedIds = ∅ := rfl

namespace YjsState

def empty : YjsState A := {
  items := #[]
  deletedIds := ∅
}

def toList (state : YjsState A) : List (YjsItem A) :=
  state.items.toList

def find? (state : YjsState A) (p : YjsItem A → Bool) : Option (YjsItem A) :=
  state.items.find? p

def addDeletedId (state : YjsState A) (id : YjsId) : YjsState A :=
  { state with deletedIds := state.deletedIds.insert id }

end YjsState

def YjsEmptyState {A} : YjsState A :=
  YjsState.empty

def ofDirectState {A : Type} (state : _root_.YjsState A) : YjsState A where
  items := state.items.map ofDirectItem
  deletedIds := state.deletedIds

@[simp] theorem ofDirectState_items {A : Type} (state : _root_.YjsState A) :
    (ofDirectState state).items = state.items.map ofDirectItem := rfl

@[simp] theorem ofDirectState_deletedIds {A : Type} (state : _root_.YjsState A) :
    (ofDirectState state).deletedIds = state.deletedIds := rfl

end Indirect
